import json

if __name__ == "__main__":
    with open("legislators-current.json", "r") as inf:
        es = json.load(inf)
        for i in range(1, 101):
            prefix = es[:i]
            with open("Instances/legislators_" + str(i) + ".json", "w") as outf:
                json.dump(es[:i], outf, indent=4)
