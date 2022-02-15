import os

if __name__ == "__main__":
    d = {}
    for fname in os.listdir("OrigInstances"):
        with open("OrigInstances/{}".format(fname), "r") as inf:
            s = inf.read()
            if s.isascii():
                d[fname] = s
    prs = sorted(d.items(), key=lambda kv: len(kv[1]))
    # make small data set
    for (fname, s) in prs[0:100]:
        with open("SmallInstances/{}".format(fname), "w") as outf:
            outf.write(s)
    # make larger data set:
    for (fname, s) in prs[len(prs)-1000:]:
        with open("Instances/{}".format(fname), "w") as outf:
            outf.write(s)
