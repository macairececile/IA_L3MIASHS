#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from copy import copy
from numbers import Number
from kernel_jalon04 import Calcul


class Ask(Calcul):
    """ Extend Calcul with queries """

    def resolution(self, idx: int, withMem: bool) -> (int, bool):
        """ surcharge de resolution """
        if idx in range(6): return super().resolution(idx, withMem)
        return self.__askUnknown(idx % 6, withMem)

    def __askUnknown(self, idx: int, withMem: bool) -> (int, bool):
        _msg = "Donnez une valeur entre -1 et 1 pour "
        a, b = self.resolution(idx, withMem)
        if b or self.inconsistance: return a, b
        _total = 0  # compteur de réponses utiles
        _queries = list(self.selectableQueries())
        _fact = []
        for x in range(len(_queries)):
            if len(list(_queries[x][1])) != 0:
                if super().get_userFact(list(_queries[x][1])[0]).discret() == 0: #on regarde si la valeur du fait est inconnu si oui, on l'ajoute
                    _fact.append(list(_queries[x][1])[0])
        f = float(input(_msg + str(_fact[0]) + ' ? : '))
        if f != 0 and f >= -1 and f <= 1: #on récupère la valeur renseignée par l'utilisateur
            self.add_knowledge(_fact[0])
            self.change_knowledge(_fact[0], float(f))
            _total += 1
        if _total == 0: return a, b
        print("<*> Il y a {} nouvelle(s) information(s)".format(_total))
        c, d = self.resolution(idx, withMem)
        return (a + c), d


class Contraposition(Calcul):
    """ contraposition """

    def resolution(self, idx: int, withMem: bool) -> (int, bool):
        """ surcharge de resolution """
        if idx in range(6): return super().resolution(idx, withMem)
        return self.__contraposition(idx % 6, withMem)

    def __contraposition(self, idx: int, withMem: bool) -> (int, bool):
        """ if failed then contraposition might help """
        a, b = self.resolution(idx, withMem)
        if b or self.inconsistance: return a, b
        # do something with self.selectableContra()
        _total = 0  # compteur des actions utiles
        _contra = list(self.selectableContra())
        for x in range(len(_contra)):
            if list(_contra[x])[1] != None:
                self.add_regle(_contra[x][1]) #ajout de la règle si element a droite non nul
                _total += 1
        if _total == 0: return a, b
        print("<*> Il y a {} nouvelle(s) règle(s)".format(_total))
        c, d = self.resolution(idx, withMem)
        return (a + c), d


class NegAsMissing(Calcul):
    """ negation is set by missing """

    def resolution(self, idx: int, withMem: bool) -> (int, bool):
        """ surcharge de resolution """
        if idx in range(6): return super().resolution(idx, withMem)
        return self.__missing(idx % 6, withMem)

    def __missing(self, idx: int, withMem: bool) -> (int, bool):
        """ if failed then missing is false """
        a, b = self.resolution(idx, withMem)
        if b or self.inconsistance: return a, b
        _total = 0  # compteur des actions utiles

        _negmiss = list(self.selectableNegation())
        for x in range(len(_negmiss)):
            if len(_negmiss[x][1]) != 0:
                _total += 1
                elem = next(iter(_negmiss[x][1]))
                self.add_knowledge(elem)
                self.change_knowledge(elem, -1)
        if _total == 0: return a, b
        print("<*> Il y a {} nouvelle(s) information(s)".format(_total))
        c, d = self.resolution(idx, withMem)
        return (a + c), d


class NegAsFailure(Calcul):
    """ negation is set by failure """

    def resolution(self, idx: int, withMem: bool) -> (int, bool):
        """ surcharge de resolution """
        if idx in range(6): return super().resolution(idx, withMem)
        return self.__failure(idx % 6, withMem)

    def __failure(self, idx: int, withMem: bool) -> (int, bool):
        """ if failed then contraposition might help """
        a, b = self.resolution(idx, withMem)
        if b or self.inconsistance: return a, b
        _total = 0  # compteur des actions utiles
        _current_goal = self.get_goals()  # sauvegarde des buts courants
        self.reset_goal()  # vidage des goals
        _negfail = self.selectableNegation()
        for x in range(len(_negfail)):
            if len(_negfail[x][1]) != 0:
                g = next(iter(_negfail[x][1]))
                rep = self.add_goal(g)
                if not super().get_userFact(g).prouvable:
                    Ask()
                if not rep or self.resolution(2, True)[1] == False:
                    l = next(iter(_negfail[x][1]))
                    self.add_knowledge(l)
                    self.change_knowledge(l, 1)
                    _total += 1
                self.reset_goal()
        for i in range(len(_current_goal)):
            self.add_goal(_current_goal[i])
        if _total == 0: return a, b
        print("<*> Il y a {} nouvelle(s) information(s)".format(_total))
        c, d = self.resolution(idx, withMem)
        return (a + c), d


class Mycin(Calcul):
    """ computation à la Mycin """

    def resolution(self, idx: int, withMem: bool) -> (int, bool):
        """ surcharge de resolution permet de bloquer
            pour l'utilisateur Calcul.resolution
            dans la classe si on avait besoin d'une méthode
            de resolution faite par Calcul il suffit d'utiliser
            la syntaxe super().resolution(int, bool)
            par exemple pour faire du chainage arrière avec mémoire
            on écrit: super().resolution(2, True)
        """
        return self.__mycin(idx, True)

    def get_evalLeft(self, left: set) -> 'Number':
        """ surcharge: a set of int => a value """
        return min([self.get_userFact(_).valeur
                    for _ in self.get_useridList(left)])

    @staticmethod
    def agregate(x: float, y: float, dec: int = 3) -> float:
        """ given 2 floats agregate the result and round it """
        if x > 0 and y > 0: return round(x + y - x * y, dec)
        if x < 0 and y < 0: return round(x + y + x * y, dec)
        if abs(x) == abs(y): return 0
        return round((x + y) / (1 - min(abs(x), abs(y))), dec)

    def resolve_conflicts(self, idx: int) -> list:
        """ given a strategy 0, 1, 2 find the rules to apply """
        _ = self.selectableRules()  # ordre croissant
        if idx == 2: return _  # toutes les règles
        _select = {}

        for r in _:
            _atom = self.get_useridList(r.droite)[0]
            _old = _select.get(_atom, None)
            if _old is None: _select[_atom] = r
            if idx == 1 and _old is not None:
                # quelle règle choisir ?
                if _old.fiabilite < r.fiabilite:
                    _select[_atom] = r
                elif _old.fiabilite == r.fiabilite:
                    if len(_old.gauche) > len(r.gauche):
                        _select[_atom] = r
                    elif len(_old.gauche) == len(r.gauche):
                        if (self.get_evalLeft(r.gauche) >
                                self.get_evalLeft(_old.gauche)):
                            _select[_atom] = r
        return list(_select.values())

    def check_discret(self, a):
        if super().get_userFact(a).discret() == 0:
            super().del_knowledge(a)

    def first_strategy(self):
        """première stratégie"""
        _todo = self.resolve_conflicts(0)
        a = []
        for g in range(len(_todo)):
            elem = list(_todo[g].droite)[0]
            f = self.get_useridFact(elem)
            a.append(f)
        _rules = list()
        for i in range(len(a)):
            if self.get_userFact(a[i]) not in self.base:
                f = super().get_idnumFact(a[i])
                for j in range(len(_todo)):
                    if list(_todo[j].droite)[0] == f:
                        _rules.append(_todo[j].idnum)
                if len(_rules) > 1:
                    minid = _rules.index(min(_rules))  # on récupère la règle avec le plus petit idnum
                    for k in range(len(_todo)):
                        if _todo[k].idnum == minid:
                            val_g = self.get_evalLeft(set(_todo[k].gauche))
                    val_d = super().get_userFact(a[i]).valeur
                    self.add_knowledge(a[i])  # on ajoute dans la base le fait
                    self.change_knowledge(a[i], val_g * val_d)
                    self.check_discret(a[i]) #on regarde la valeur discrete du fait ajoutée, si nulle, on enlève de base
                else:
                    for k in range(len(_todo)):
                        if _todo[k].idnum == _rules[0]:
                            val_g = self.get_evalLeft(set(_todo[k].gauche))
                    val_d = super().get_userFact(a[i]).valeur
                    self.add_knowledge(a[i])  # on ajoute dans la base le fait
                    self.change_knowledge(a[i], val_g * val_d)
                    self.check_discret(a[i])
                _rules = list()
        print(self.base)

    def second_strategy(self):
        """seconde stratégie"""
        _todo = self.resolve_conflicts(1)
        a = []
        _rules = []
        for g in range(len(_todo)):
            elem = list(_todo[g].droite)[0]
            f = self.get_useridFact(elem)
            a.append(f)
        for i in range(len(a)):
            val_g = 0
            f = super().get_idnumFact(a[i])
            for j in range(len(_todo)):
                if list(_todo[j].droite)[0] == f:
                    _rules.append(_todo[j].idnum)
            for k in range(len(_todo)):
                if _todo[k].idnum == _rules[0]:
                    val_g = self.get_evalLeft(set(_todo[k].gauche)) #récupère la valeur a gauche de la règle correspondant au fait
            val_d = super().get_userFact(a[i]).valeur
            if val_d == 0:
                self.add_knowledge(a[i])  # on ajoute dans la base le fait
                self.change_knowledge(a[i], val_g)
                self.check_discret(a[i])
            elif val_d != 0:
                self.add_knowledge(a[i])  # on ajoute dans la base le fait
                self.change_knowledge(a[i], val_d)
                self.check_discret(a[i])
            _rules = []
        print(self.base)

    def third_strategy(self):
        """troisième stratégie incomplète"""
        _todo = self.resolve_conflicts(2)
        a = []
        _rules = []
        for g in range(len(_todo)):
            elem = list(_todo[g].droite)[0]
            f = self.get_useridFact(elem)
            a.append(f)
        return 0


    def __mycin(self, idx: int, withMem: bool) -> (int, bool):
        """ working in dfs bfs with memory """
        if idx == 0:  # on applique la 1ère stratégie
            """"""
            self.first_strategy()
        elif idx == 1:  # on applique la 2ème stratégie
            """"""
            self.second_strategy()
        elif idx == 2:  # on applique la troisième stratégie
            """"""
            self.third_strategy()


if __name__ == "__main__":
    _rules = """ a -> b .7
        a -> c .5
        a -> d .3
        b -> e .5
        c -> e .8
        d -> e """
    c = Mycin()
    for line in _rules.split('\n'):
        if len(line) == 0: continue
        c.add_regle(line)

    print('règles:', c.rules)
    print('symboles:', c.table)

    c.add_knowledge('a')
    print('base:', c.base)
    for i in range(3):
        print("règles sélectionnées pour stratégie {}".format(i))
        print(c.resolve_conflicts(i))

    print("#{}#".format('=' * 23))

    for x in 'bcd': c.add_knowledge(x)
    c.change_knowledge('a', 1)
    c.change_knowledge('b', .7)
    c.change_knowledge('c', .5)
    c.change_knowledge('d', .3)
    print('base:', c.base)

    for i in range(3):
        print("règles sélectionnées pour stratégie {}".format(i))
        print(c.resolve_conflicts(i))

    c.resolution(1, True)

    # c = NegAsMissing()
    # c.add_regle('sacs -> container')
    # c.add_regle('grosse-quantité -> container')
    # c.add_regle('asperges & moyenne-quantité -> cageots')
    # c.add_regle('choux-fleurs & petite-quantité -> cageots')
    # c.add_regle('délais-très-courts -> pressé')
    # c.add_regle('délais-courts & fragile -> pressé')
    # c.add_regle('container & hors-France & pressé -> express')
    # c.add_regle('container & France & pas-pressé -> péniche')
    # c.add_regle('container & France & pressé -> camion')
    # c.add_regle('cageots & hors-France & pas-fragile -> camion')
    # c.add_regle('fragile & hors-France -> avion')
    # c.add_regle('asperges & pas-container -> fragile')
    # c.add_regle('ramassage-automatique -> sacs')
    # c.add_regle('cageots -> pas-sacs')
    # c.add_knowledge('choux-fleurs')
    # c.change_knowledge('choux-fleurs', 1)
    # c.add_knowledge('grosse-quantité')
    # c.change_knowledge('grosse-quantité', 1)
    # c.add_knowledge('France')
    # c.change_knowledge('France', 1)
    # c.add_goal('camion')
    # print(c.resolution(6, True))


