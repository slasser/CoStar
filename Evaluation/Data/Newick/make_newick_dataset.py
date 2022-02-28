import os

if __name__ == "__main__":
    for fname in os.listdir("."):
        if fname.endswith(".nex"):
            num_species = fname.split("_")[0]
            print(num_species)
            with open(fname, "r") as inf:
                trees = [line.split(" ")[3] for line in inf if line.startswith("tree")]
                for i in range(10, 35, 5):
                    with open("Instances/{}_species_{}_trees.txt".format(num_species, i), "w") as outf:
                        outf.write("".join(trees[:i]))
                """
                for line in inf:
                    if line.startswith("tree"):
                        (_, instance_num, _, tree) = line.split(" ")
                        with open("Instances/{}_species_{}.tree".format(num_species, instance_num), "w") as outf:
                            outf.write(tree)
                """
                        
