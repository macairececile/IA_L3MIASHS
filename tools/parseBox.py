#!/usr/bin/env python3
# -*- coding: utf-8 -*-

__author__ = "mmc <marc-michel dot corsini at u-bordeaux dot fr>"
__date__ = "20.02.19"
__usage__ = "Parsing toolbox projet 2018/2019"
__update__ = "26.03.19 15h"

import re

def parsingRule(regle:str) -> tuple:
    """ regle := gauche -> droite
        gauche := char | char & gauche
        droite := char | char & droite
    """
    l = [ x.split('&') for x in regle.split('->') ]
    _l = [ x.strip() for x in l[0] ]
    _r = [ x.strip() for x in l[1] ]
    return tuple(_l), tuple(_r)

def parseRule(regle:str) -> tuple:
    """ regle := gauche -> droite
        gauche := char | char & gauche
        droite := char 
        fiab := float
    """
    l = [ x.split('&') for x in regle.split('->') ]
    _l = [ x.strip() for x in l[0] ]
    _r = l[1][0].split() 
    if len(_r) == 1:
        return tuple(_l), tuple(_r), 1
    else:
        return tuple(_l), tuple([_r[0]]), float(_r[1])

def parseExpressionRule(regle:str) -> tuple:
    exp = re.compile(r"""
    ^\s*(?P<gauche>.+)\s*->\s*(?P<droite>.+)\s*(?P<val>(0?\.\d+)){0,1}\s*$
""")
    m = exp.match(regle)
    print(m.groups())
                     

    
def reader(c: 'Calcul', rules:str) -> set:
    """ parse a string of rules and provide a set of atoms """
    if hasattr(c, 'clear'): c.clear() # ensure Fait.ID = Regle.ID = 0
    _vocabulaire = set()
    _str = "#{0} {1} {0}#".format("="*11, "rules")
    print(_str)
    for line in rules.split("\n"):
        if len(line) == 0: continue
        print(">> {}".format(line))
        c.add_regle(line)
        for mot in line.split():
            if mot[0].isalpha(): _vocabulaire.add(mot)
    print("#{}#".format("="*(len(_str)-2)))

    return _vocabulaire

def trace(c:'Calcul', vocabulaire:dict):
    """ 
       provide a display of non 0 atoms
    """
    print("{0} {1} {0}".format("="*7,
                               "Trace for {}".format(c.__class__.__name__)))
    for atom in vocabulaire:
        _f = c.get_userFact(atom)
        if _f.valeur != 0:
            print("{}: {}".format(atom, _f.valeur))
    print("{}".format("="*(16+5)))
