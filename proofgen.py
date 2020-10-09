from mmverify import MM, MMError, MMKeyError
from random import choice, randint, choices
from collections import Counter
import matplotlib.pyplot as plt
import pickle

mm = MM()

mm.consume(open("set.mm"), verify=False)
print("Read file")
labels = list(mm.labels.keys())

c = Counter()
labelstats = pickle.load(open("labelstats.pickle", "rb"))

c_labels, c_weights = zip(*labelstats.items())

generated = None

def generate():
    global generated
    generated = choices(c_labels, c_weights, k=100000)

generate()

print("Read labelstats")

fail = 0
success = 0
for i in range(10000000):

    if len(generated) == 0:
        generate()

    label = f"rgenx-{success}"
    n = randint(3,10)
    stat = generated[:n]#[weighted_choice() for i in range(randint(3,6))]
    del generated[:n]



    #print(stat)
    """
    steptyp, stepdat = mm.labels[stat[0]]

    if steptyp in ["$a", "$p"]:
        (distinct, mand_var, hyp, result) = stepdat
    print(steptyp)
    """

    try:
        result = mm.prove(label, None, stat)
    except MMError as e:
        #print(dir(e))
        c[str(e)] += 1
        fail += 1
        continue

    if result[0] == "|-":
        print("proved", stat, " ".join(result))
        #mm.labels[label] = ('$p', mm.fs.make_assertion(proof))
        proof = f"{label} $p {' '.join(result)} $= {' '.join(stat)} $."
        mm.consume(proof)
        success += 1
        labels = list(mm.labels.keys())

    #

    #mm.consume(proof)
#print(mm.labels)
#print(c)
print(c.most_common(10))
print(sum(c.values()), success)
