#!/usr/bin/env python

import os
import sys

if __name__ == "__main__":
    skelton = ""
    with open("coq/hint_sem_props_resolve_skeleton.v.skeleton") as f:
        skeleton = f.read()

    rules = []

    with open("rules.txt") as f:
        for line in f.readlines():
            args = line.split(' ')
            rule = args[0]
            args = (' '.join(args[1:]))[:-1]
            filename = "coq/hint_sem_props_resolve_%s.v" % rule
            content = skeleton.replace("$1", rule).replace("$2", args)
            rules.append(rule)
            
            with open(filename, "w") as g:
                g.write(content)

    with open("rules.import.txt", "w") as f:
        for rule in rules:
            f.write("Require Import hint_sem_props_resolve_%s.\n" % rule)
