#!/usr/bin/env python3
# mmverify.py -- Proof verifier for the Metamath language
# Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License

# To run the program, type
#   $ python3 mmverify.py < set.mm 2> set.log
# and set.log will have the verification results.

# (nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
# after a $e hypothesis in the same scope, even though this is allowed by
# the Metamath spec.  This is not a serious limitation since it can be
# met by rearranging the hypothesis order.
# (rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
# (sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
# and file inclusion

import sys
import itertools
import collections
import os.path
import io

verbosity = 0

class MMError(Exception): pass
class MMKeyError(MMError, KeyError): pass

def vprint(vlevel, *args):
	"""Prints *args if vlevel is greater than the global verbosity"""
	if verbosity >= vlevel: print(*args, file=sys.stderr)

class toks:
	"""Tokenizer

	Only self.readc and self.readstat are used by the MM class.
	Each function calls the function before it, where each facilitates a special function
	(reading files, including files, discarding of comments, returning full statements).
	"""

	def __init__(self, lines):
		"""Receives open file.

		Args:
			lines: A file descriptor
		"""
		self.lines_buf = [lines]
		self.tokbuf = []
		self.imported_files = set()

	def read(self):
		"""
		Cares about reading files and returning the next token.

		Reads and splits the next line if the token buffer is empty.
		Reads the next token.

		Returns:
			A single token or None if the buffer is empty
		"""

		while self.tokbuf == []:
			line = self.lines_buf[-1].readline()
			if not line:
				self.lines_buf.pop().close()
				if not self.lines_buf: return None
			else:
				self.tokbuf = line.split()
				self.tokbuf.reverse()
		return self.tokbuf.pop()

	def readf(self):
		"""
		Cares about including yet unimported files.

		1. Reads a token.
		2. If it is an import statement, opens and appends the file to the line buffer and reads the next token. Goto 1, else continue.
		3. Returns the next token.

		Returns:
			A single token or None if the buffer is empty
		"""

		tok = self.read()
		while tok == '$[':
			filename = self.read()
			endbracket = self.read()
			if endbracket != '$]':
				raise MMError('Inclusion command not terminated')
			filename = os.path.realpath(filename)
			if filename not in self.imported_files:
				self.lines_buf.append(open(filename, 'r'))
				self.imported_files.add(filename)
			tok = self.read()
		return tok

	def readc(self):
		"""
		Skips comments.

		Reads and returns the next token, skips comments.

		Returns:
			A single token or None if the buffer is empty
		"""

		while 1:
			tok = self.readf()
			if tok == None: return None
			if tok == '$(':
				while tok != '$)':
					tok = self.read()
			else:
				return tok

	def readstat(self):
		"""
		Returns a single statement

		Returns:
			list of strings (tokens)
		"""

		stat = []
		tok = self.readc()
		while tok != '$.':
			if tok == None: raise MMError('EOF before $.')
			stat.append(tok)
			tok = self.readc()
		return stat

class Frame:
	"""
	Each frame stores all information associated with a local scope:
	- constants
	- variables
	- distinct variable declaration
	- floating hypotheses
	- essential hypotheses

	Frames are stored in the FrameStack (a list).

	"""
	def __init__(self):
		self.c = set()
		self.v = set()
		self.d = set()
		self.f = []
		self.f_labels = {}
		self.e = []
		self.e_labels = {}

class FrameStack(list):
	"""
	A Framestack subclasses a list and provides methods for adding and looking up:
	- constants
	- variables
	- distinct variable declaration
	- floating hypotheses
	- essential hypotheses
	on the current (active) frame.

	It ensures that there are no name collisions and raises an MMError exception otherwise.
	"""

	def push(self):
		"""Pushes a new, empty frame on the stack"""
		self.append(Frame())

	def add_c(self, tok):
		"""Adds a constant to the current frame

		Args:
			A single string (token)

		Raises:
			MMError: when the constant is already defined as constant or variable in the current frame
		"""
		frame = self[-1]
		if tok in frame.c: raise MMError('const already defined in scope')
		if tok in frame.v:
			raise MMError('const already defined as var in scope')
		frame.c.add(tok)

	def add_v(self, tok):
		"""Adds a variable to the current frame

		Args:
			A single string (token)

		Raises:
			MMError: when the variable is already defined as variable or constant in the current frame
		"""
		frame = self[-1]
		if tok in frame.v: raise MMError('var already defined in scope')
		if tok in frame.c:
			raise MMError('var already defined as const in scope')
		frame.v.add(tok)

	def add_f(self, var, kind, label):
		"""Adds a floating hypothesis to the current frame

		Example:
			test $f wff phi $.
			add_f("phi", "wff", "test")

		Args:
			var (string): An active variable
			kind (string): An active constant
			label (string): The label of this floating hypothesis

		Raises:
			MMError: when the constant or variable are not defined in this scope or if the variable is already used in another floating hypothesis.
		"""
		if not self.lookup_v(var):
			raise MMError('var in $f not defined: {0}'.format(var))
		if not self.lookup_c(kind):
			raise MMError('const in $f not defined {0}'.format(kind))
		frame = self[-1]
		if var in frame.f_labels.keys():
			raise MMError('var in $f already defined in scope')
		frame.f.append((var, kind))
		frame.f_labels[var] = label

	def add_e(self, stat, label):
		"""Adds an essential hypothesis to the current frame

		Args:
			stat (list of strings): An active constant followed by zero or more active math symbols
			label (string): The label of this essential hypothesis
		"""
		frame = self[-1]
		frame.e.append(stat)
		frame.e_labels[tuple(stat)] = label

	def add_d(self, stat):
		"""Adds a distinct variable statement to the current frame

		Splits up compound distinct variable statements into simple ones.
		"""
		frame = self[-1]

		# The min/max functions ensure that the elements are uniquely ordered (always (a,b), not (b,a)), where a<b.
		frame.d.update(((min(x,y), max(x,y))
						for x, y in itertools.product(stat, stat) if x != y))

	def lookup_c(self, tok):
		"""Looks up if a constant is declared, starting from the current frame and going down the stack

		Args:
			A single string (token)

		Returns:
			True if the constant is declared in any of the frames in the stack, False otherwise
		"""
		return any((tok in fr.c for fr in reversed(self)))

	def lookup_v(self, tok):
		"""Looks up if a variable is declared, starting from the current frame and going down the stack

		Args:
			A single string (token)

		Returns:
			True if the variable is declared in any of the frames in the stack, False otherwise
		"""
		return any((tok in fr.v for fr in reversed(self)))

	def lookup_f(self, var):
		"""Returns the associated floating hypothesis label of a variable in the frame stack.

		Args:
			var (string): An active variable

		Returns:
			string: The label of the floating hypothesis

		Raises:
			MMKeyError: If var is not associated with a floating hypothesis.
		"""

		for frame in reversed(self):
			try: return frame.f_labels[var]
			except KeyError: pass
		raise MMKeyError(var)

	def lookup_d(self, x, y):
		"""Looks up if x and y are declared as distinct.

		Args:
			x (string): a variable
			y (string): a variable

		Returns:
			True if they are distinct, False if not.
		"""
		return any(((min(x,y), max(x,y)) in fr.d for fr in reversed(self)))

	def lookup_e(self, stmt):
		"""Returns the associated essential hypothesis label of a statement in the frame stack.

		Args:
			stmt (list of strings): A statement

		Returns:
			string: The label of the essential hypothesis

		Raises:
			MMKeyError: If var is not associated with a floating hypothesis.
		"""
		stmt_t = tuple(stmt)
		for frame in reversed(self):
			try: return frame.e_labels[stmt_t]
			except KeyError: pass
		raise MMKeyError(stmt_t)

	def make_assertion(self, stat):
		"""

		Args:
			stat (list of strings): A statement

		Returns:

		"""

		# The active frame
		frame = self[-1]

		# All essential hypotheses in all frames
		e_hyps = [eh for fr in self for eh in fr.e]

		# All mandatory variables
		mand_vars = {tok for hyp in itertools.chain(e_hyps, [stat])
						 for tok in hyp if self.lookup_v(tok)}

		# All distinct variable pairs in all frames
		dvs = {(x,y) for fr in self for (x,y) in
			   fr.d.intersection(itertools.product(mand_vars, mand_vars))}

		f_hyps = collections.deque()
		for fr in reversed(self):
			for v, k in reversed(fr.f):
				if v in mand_vars:
					f_hyps.appendleft((k, v))
					mand_vars.remove(v)

		vprint(18, 'ma:', (dvs, f_hyps, e_hyps, stat))
		return (dvs, f_hyps, e_hyps, stat)

class MM:
	"""
	Metamath class.

	Stores all global labels (axioms, proofs, floating)

	"""
	def __init__(self):
		self.fs = FrameStack()
		self.labels = {}
		self.stepstats = collections.Counter()

	def consume(self, thing, verify=True):
		if isinstance(thing, io.IOBase):
			self.read(toks(thing), verify)
		elif isinstance(thing, str):
			self.read(toks(io.StringIO(thing)), verify)
		else:
			raise Exception("Unknown thing", thing)

	def read(self, toks, verify=True):
		"""
		Reads a file and verifies on the go.
		TODO:
		- add a verify=bool argument (to just syntax check?)
		- result caching

		Args: a toks class instance

		Raises:
			MMError: on syntax errors
		"""
		self.fs.push()
		label = None
		tok = toks.readc()
		while tok not in (None, '$}'):
			if tok == '$c':
				# Add all constants in a $c statement to the active frame
				for tok in toks.readstat(): self.fs.add_c(tok)
			elif tok == '$v':
				# Add all variables in a $v statement to the active frame
				for tok in toks.readstat(): self.fs.add_v(tok)
			elif tok == '$f':
				stat = toks.readstat()
				if not label: raise MMError('$f must have label')
				if len(stat) != 2: raise MMError('$f must have be length 2')
				vprint(15, label, '$f', stat[0], stat[1], '$.')
				self.fs.add_f(stat[1], stat[0], label)
				self.labels[label] = ('$f', [stat[0], stat[1]])
				label = None
			elif tok == '$a':
				if not label: raise MMError('$a must have label')
				self.labels[label] = ('$a',
									  self.fs.make_assertion(toks.readstat()))
				label = None
			elif tok == '$e':
				if not label: raise MMError('$e must have label')
				stat = toks.readstat()
				self.fs.add_e(stat, label)
				self.labels[label] = ('$e', stat)
				label = None
			elif tok == '$p':
				if not label: raise MMError('$p must have label')
				stat = toks.readstat()
				proof = None
				try:
					i = stat.index('$=')
					proof = stat[i + 1:]
					stat = stat[:i]
				except ValueError:
					 raise MMError('$p must contain proof after $=')
				vprint(1, 'verifying', label)
				if verify:
					self.verify(label, stat, proof)

				"""
				if proof[0] == '(': proof = self.decompress_proof(stat, proof)

				for step in proof:
					self.stepstats[step] += 1
				"""

				self.labels[label] = ('$p', self.fs.make_assertion(stat))
				#print(len(self.labels), label)
				label = None
			elif tok == '$d': self.fs.add_d(toks.readstat())
			elif tok == '${': self.read(toks, verify)
			elif tok[0] != '$': label = tok
			else: print('tok:', tok)
			tok = toks.readc()
		self.fs.pop()

	def apply_subst(self, stat, subst):
		"""
		Applies a substitution map to a statement.

		Args:
			stat (list of strings): A statement
			subst (dict(string, list of strings)): A dictionary mapping from values to their substitution targets

		Returns:
			(list of strings): The statement with all substitutions applied.
		"""
		result = []
		for tok in stat:
			if tok in subst: result.extend(subst[tok])
			else: result.append(tok)
		vprint(20, 'apply_subst', (stat, subst), '=', result)
		return result

	def find_vars(self, stat):
		"""
		Given a statement, returns a list of all its variables.

		Args:
			stat: A statement

		Returns:
			(list of strings): list of variables in stat
		"""
		vars = []
		for x in stat:
			if not x in vars and self.fs.lookup_v(x): vars.append(x)
		return vars

	def decompress_proof(self, stat, proof):
		dm, mand_hyp_stmts, hyp_stmts, stat = self.fs.make_assertion(stat)

		mand_hyps = [self.fs.lookup_f(v) for k, v in mand_hyp_stmts]
		hyps = [self.fs.lookup_e(s) for s in hyp_stmts]

		labels = mand_hyps + hyps
		hyp_end = len(labels)
		ep = proof.index(')')
		labels += proof[1:ep]
		compressed_proof = ''.join(proof[ep+1:])

		vprint(5, 'labels:', labels)
		vprint(5, 'proof:', compressed_proof)

		proof_ints = []
		cur_int = 0

		for ch in compressed_proof:
			if ch == 'Z': proof_ints.append(-1)
			elif 'A' <= ch and ch <= 'T':
				cur_int = (20*cur_int + ord(ch) - ord('A') + 1)
				proof_ints.append(cur_int - 1)
				cur_int = 0
			elif 'U' <= ch and ch <= 'Y':
				cur_int = (5*cur_int + ord(ch) - ord('U') + 1)
		vprint(5, 'proof_ints:', proof_ints)

		label_end = len(labels)
		decompressed_ints = []
		subproofs = []
		prev_proofs = []
		for pf_int in proof_ints:
			if pf_int == -1: subproofs.append(prev_proofs[-1])
			elif 0 <= pf_int and pf_int < hyp_end:
				prev_proofs.append([pf_int])
				decompressed_ints.append(pf_int)
			elif hyp_end <= pf_int and pf_int < label_end:
				decompressed_ints.append(pf_int)

				step = self.labels[labels[pf_int]]
				step_type, step_data = step[0], step[1]
				if step_type in ('$a', '$p'):
					sd, svars, shyps, sresult = step_data
					nshyps = len(shyps) + len(svars)
					if nshyps != 0:
						new_prevpf = [s for p in prev_proofs[-nshyps:]
									  for s in p] + [pf_int]
						prev_proofs = prev_proofs[:-nshyps]
						vprint(5, 'nshyps:', nshyps)
					else: new_prevpf = [pf_int]
					prev_proofs.append(new_prevpf)
				else: prev_proofs.append([pf_int])
			elif label_end <= pf_int:
				pf = subproofs[pf_int - label_end]
				vprint(5, 'expanded subpf:', pf)
				decompressed_ints += pf
				prev_proofs.append(pf)
		vprint(5, 'decompressed ints:', decompressed_ints)

		return [labels[i] for i in decompressed_ints]

	def prove(self, stat_label, stat, proof):
		# The proof stack. Floating and essential hypotheses are put on top, axioms and proofs transform it.
		# This is a tree-like structure, since essential hypotheses are appended as lists
		stack = []

		# If the proof is in compressed form, decompress it
		if proof[0] == '(': proof = self.decompress_proof(stat, proof)
		#print(proof)
		# Iterate over every label in the proof sequence
		for label in proof:
			steptyp, stepdat = self.labels[label]
			vprint(10, label, ':', self.labels[label])

			# If the label points to
			# - an axiom or proof:
			# - a floating or essential hypothesis: push it onto the stack
			if steptyp in ('$a', '$p'):
				(distinct, mand_var, hyp, result) = stepdat
				#print(label, steptyp, distinct, mand_var, hyp, result)
				#print(stack)
				vprint(12, stepdat)
				# The number of elements to be popped from the top of the stack
				npop = len(mand_var) + len(hyp)
				# The new length of the stack (stack pointer), points to the element before the first input
				sp = len(stack) - npop
				# Raise an exception if the stack does not have enough elements
				if sp < 0: raise MMError('stack underflow')

				subst = {}
				for (k, v) in mand_var:
					entry = stack[sp]
					if entry[0] != k:
						raise MMError(
							("stack entry ({0}, {1}) doesn't match " +
							 "mandatory var hyp {2!s}").format(k, v, entry))
					subst[v] = entry[1:]
					sp += 1
				vprint(15, 'subst:', subst)

				for x, y in distinct:
					vprint(16, 'dist', x, y, subst[x], subst[y])
					x_vars = self.find_vars(subst[x])
					y_vars = self.find_vars(subst[y])
					vprint(16, 'V(x) =', x_vars)
					vprint(16, 'V(y) =', y_vars)
					for x, y in itertools.product(x_vars, y_vars):
						if x == y or not self.fs.lookup_d(x, y):
							raise MMError("disjoint violation: {0}, {1}"
										  .format(x, y))
				for h in hyp:
					entry = stack[sp]
					subst_h = self.apply_subst(h, subst)
					if entry != subst_h:
						raise MMError(("stack entry {0!s} doesn't match " +
									   "hypothesis {1!s}")
									   .format(entry, subst_h))
					sp += 1

				# Delete all inputs to the proof
				del stack[len(stack) - npop:]
				# Push the substitution result to the stack
				stack.append(self.apply_subst(result, subst))
			elif steptyp in ('$e', '$f'): stack.append(stepdat)

            # Print the stack
			vprint(12, 'st:', stack)

		# If, at the end of the proof, the stack contains anything else than the proof assertion, raise an exception
		if len(stack) != 1: raise MMError('stack has >1 entry at end')

		return stack[0]

	def verify(self, stat_label, stat, proof):
		"""
		Verifies a proof in the current scope.

		Args:
			stat_label (string): The proof label
			stat (list of strings): The assertion of the proof
			proof (list of strings): The proof itself, a sequence of labels

		Returns: None if the proof is valid, otherwise raises an exception

		Raises:
			MMError: invalid proof
		"""

		result = self.prove(stat_label, stat, proof)


		if result != stat: raise MMError("assertion proved doesn't match")

	def dump(self):
		print(self.labels)

if __name__ == "__main__":
	mm = MM()
	mm.consume(open("prop.mm"))
	#mm.consume(open("proof.mm").read())
	#mm.dump()

"""
if __name__ == '__main__':
	mm = MM()
	mm.read(toks(sys.stdin))
	#mm.dump()
"""
