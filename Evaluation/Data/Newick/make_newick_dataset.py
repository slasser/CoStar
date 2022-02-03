if __name__ == "__main__":
    with open("100_trees.nex", "r") as inf:
        ls = [l for l in inf if l.startswith("tree")]
        for l in ls:
            print(len(l))
