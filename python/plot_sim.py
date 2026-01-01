import csv
import matplotlib.pyplot as plt

t, psi = [], []
with open("sim.csv", newline="") as f:
    r = csv.DictReader(f)
    for row in r:
        t.append(int(row["t"]))
        psi.append(float(row["psi"]))

plt.figure()
plt.plot(t, psi)
plt.xlabel("t")
plt.ylabel("psi")
plt.title("Coherence trajectory (psi)")
plt.show()
