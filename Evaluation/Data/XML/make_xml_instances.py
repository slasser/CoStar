import os

def make_ascii_instances(in_dir, out_dir):
    for fname in os.listdir(in_dir):
        with open("{}/{}".format(in_dir, fname), "r") as inf:
            s = inf.read()
            if s.isascii():
                with open("{}/{}".format(out_dir, fname), "w") as outf:
                    outf.write(s)

def make_instances(in_dir, out_dir):
    # make mapping from filenames to their contents
    d = {}
    for fname in os.listdir(in_dir):
        with open("{}/{}".format(in_dir, fname), "r") as inf:
            d[fname] = inf.read()
    # take a subset of files with a range of sizes
    prs = sorted(d.items(), key=lambda kv: len(kv[1]))
    for i, (fname, s) in enumerate(prs):
        if i % 10 == 0:
            with open("{}/{}".format(out_dir, fname), "w") as outf:
                outf.write(s)

if __name__ == "__main__":
    make_ascii_instances("OrigInstances", "AsciiInstances")
    make_instances("AsciiInstances", "Instances")
    
"""    # make small data set
    for (fname, s) in prs[0:100]:
        with open("SmallInstances/{}".format(fname), "w") as outf:
            outf.write(s)

d[fname] = s
    prs = sorted(d.items(), key=lambda kv: len(kv[1]))
    for (fname, s) in prs[len(prs)-1000:]:
        with open("Instances/{}".format(fname), "w") as outf:
            outf.write(s)
"""
