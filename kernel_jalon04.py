#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from numbers import Number

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

class Diagnostic:
    """ string formatted for proof """
    __slots__ = ('__storage', '__last')
    def __init__(self):
        self.__storage = ""
        self.__last = []
        
    def __str__(self): return self.__storage
    def add(self, idnum:int, atom:str, val:Number):
        _msg = "Utilisation de R{:02d} {} vaut {}\n".format(idnum, atom, val)
        self.__last.append(-len(_msg))
        self.__storage += _msg
    def add_failure(self, idnum:int, atom:str):
        _msg = "R{:02d} failed for {}\n".format(idnum, atom)
        self.__last.append(-len(_msg))
        self.__storage += _msg
        
    def remove(self):
        if len(self.__last) > 0:
            _sz = self.__last.pop(-1)
            self.__storage = self.__storage[:_sz]
        
    def clear(self):
        self.__storage = ""
        self.__last.clear()
        
class Fait:
    """ Atomic part of knowledge """
    ID = 0
    __slots__ = ('__id', 'valeur', 'gauche', 'droite')
    def __init__(self, vv:float=0.) -> None:
        """ require vv in [-1, 1]
            ensure unique identifier
            provide idnum: unique id
            provide valeur: belief value
            provide gauche: frozenset of regle.idnum
            ensure forall x in gauche, self.idnum in regle.gauche
            provide droite: frozenset of regle.idnum
            ensure forall x in droite, self.idnum in regle.droite
        """
        self.__id = self.ID
        Fait.ID += 1
        self.valeur = vv
        self.gauche = []
        self.droite = []

    @property
    def idnum(self) -> int:
        """ unique id """
        return self.__id

    @property
    def prouvable(self) -> bool:
        """ one is provable if belongs to a right part of a rule """
        return self.droite != []

    def __str__(self) -> str:
        """ long display """
        _s = "F{0.idnum:02d} valeur {0.valeur:+.2f}".format(self)
        _s += "\n"
        _s += "gauche: ["+','.join([str(_) for _ in self.gauche])+"]\n"
        _s += "droite: ["+','.join([str(_) for _ in self.droite])+"]\n"
        return _s

    def __repr__(self) -> str:
        """ short display """
        return "F{0.idnum:02d} valeur {0.valeur:+.2f}".format(self)

    def discret(self, theta=0.2) -> int:
        """ 3-states [-1, -theta[ [-theta, theta] ]theta 1] """
        if self.valeur > theta: return 1
        if self.valeur < -theta: return -1
        return 0

        
class Regle:
    """ <conditions> -> <conclusions> """
    ID = 0
    def __init__(self, gauche:list, droite:list, fiab:float=1.) -> None:
        """
        require gauche list of Fait.id
        require droite list of Fait.id
        require fiab in [0, 1]
        """
        self.__id = self.ID
        Regle.ID += 1
        self.__left = frozenset(gauche)
        self.__right = frozenset(droite)
        self.__fiabilite = fiab

    def __str__(self) -> str:
        """ rich display """
        s = "R{0.idnum} :"
        #for x in self.gauche:
        #    s += str(x)+', '
        #s = s[:-2]
        s += ','.join([str(x) for x in self.gauche])
        s += ' -> '
        s += ','.join([str(x) for x in self.droite])
        return s.format(self)

    def __repr__(self) -> str:
        """ short output """
        return "R{0.idnum} {0.gauche} -> {0.droite}".format(self)
        
    @property
    def idnum(self) -> int:
        """ unique id of the rule """
        return self.__id
    @property
    def gauche(self) -> set:
        """ set of idnum belonging to the left part of the rule """
        return self.__left
    @property
    def droite(self) -> set:
        """ set of idnum belonging to the right part of the rule """
        return self.__right
    @property
    def fiabilite(self) -> float:
        """ the fiability of the rule """
        return max(0., min(self.__fiabilite, 1.))
    @fiabilite.setter
    def fiabilite(self, val):
        """ update the rule's fiability 
            no modification allowed at this stage
        """
        pass

class Calcul:
    """ the core of the system 
        - a table linking external name and internal name
        - a list of rules <premisses> -> <conclusions>
        - a list of known facts
        - a list of goals
    """
    def __init__(self) -> None:
        self.__symbTab = {}
        self.__reverseSym = {}
        self.__negation = {}
        self.__rules = []
        self.__base = set()
        self.__query = set()
        self.__diag = Diagnostic()
        self.__neg = "not- non- pas-".split()
        self.__inconsistance = False
        
    def clear(self):
        """ reset main variables """
        self.__symbTab.clear()
        self.__reverseSym.clear()
        self.__negation.clear()
        self.__rules.clear()
        self.__base.clear()
        self.__query.clear()
        self.__diag.clear()
        self.__inconsistance = False
        Fait.ID = Regle.ID = 0

    def __str__(self) -> str:
        """ display the state of the system 
            * the facts and their belief
            * the rules
        """
        _s = ''
        _s += "Règles\n"
        for r in self.__rules:
            _s += str(r) + '\n'
        _s += "Faits connus\n"
        for k in self.__base:
            _s += str(self.__symbTab[k]) + '\n'
        _s += '='*7+'\n'
        return _s

    def __repr__(self) -> str:
        """ short representation """
        return ("Table des symboles {} valeurs, Base {} Fait(s),"
                " {} Règle(s)".format(len(self.table), len(self.base),
                                      len(self.rules)))

    def __find_fact(self, key:str) -> Fait:
        """ helper, get an old Fact or provide a new one """
        if key not in self.__symbTab:
            _nf = Fait()
            self.__symbTab[key] = _nf
            self.__reverseSym[_nf.idnum] = key
        return self.__symbTab[key]
    
    def add_regle(self, regle:str) -> None:
        """ regle a1 & a2 & .. & an -> c 
        ensure that new facts are created and stored
        ensure that fact is updated when appearing in a rule
        """
        _g, _d, fiab = parseRule(regle)
        _left = [ self.__find_fact(x).idnum for x in _g ]
        _right = [ self.__find_fact(x).idnum  for x in _d ]
        _nRule = Regle(_left, _right, fiab)
        self.__rules.append(_nRule)
        for x in set(_g):
            self.__symbTab[x].gauche.append(_nRule.idnum)
        for x in set(_d):
            self.__symbTab[x].droite.append(_nRule.idnum)

    def check_knowledge(self, keysymb:str) -> bool:
        """ check that keysymb is in base """
        return keysymb in self.__base
    
    def add_knowledge(self, keysymb:str) -> None:
        """ 
            require keysymb not in base
            if keysymb is not in symtab
               ensure a new fact is created with belief=0
            ensure base has changed
        """
        _f = self.__find_fact(keysymb)
        self.del_goal(keysymb)
        self.__base.add(keysymb)
        _okey = self.get_opposition(keysymb)
        if _okey is not None:
            self.del_goal(_okey)            
            self.__base.add(_okey)

    def del_knowledge(self, keysymb:str) -> None:
        """
           require keysymb in symtab
           ensure fact related to keysymb is no longer in base
        """
        self.__base.discard(keysymb)
        _okey = self.get_opposition(keysymb)
        self.__base.discard(_okey) # even None should work

    def change_knowledge(self, keysymb:str, val:float) -> bool:
        """
            require keysymb in symtab
            if fact related to keysymb in base: return True
            else: return False

            ensure fact related to keysymb has valeur==val
        """
        if keysymb in self.__query: return False
        _f = self.__symbTab[keysymb]
        _f.valeur = val
        self.__updateNot(keysymb)
        return self.check_knowledge(keysymb)
            
    def reset_knowledge(self) -> None:
        """
           remove any information stored in base
           ensure symbtab unchanged
        """
        self.__base.clear()

    #================= gestion opposition =========================#
    
    def __check_consistancy(self, k1:str, k2:str) -> int:
        """ we know all is fine
            - need only goal with goal and base with base
            - we know base cap goals = empty
        """
        if k1 in self.__base:
            if k2 in self.__query:
                self.__base.discard(k1)
                self.__query.discard(k2)
            else: self.__base.add(k2)
        elif k1 in self.__query:
            if k2 in self.__base:
                self.__base.discard(k2)
                self.__query.discard(k1)
            else: self.__query.add(k2)
        else: # k1 nowhere
            if k2 in self.__base: self.__base.add(k1)
            elif k2 in self.__query: self.__query.add(k1)
        return 1
    
    def add_opposition(self, key1:str, key2:str) -> int:
        """ :return:  1 all is fine
            :return:  0 partial failure (opposition)
            :return: -1 total failure (creation+opposition)
        """
        # aucun n'existe
        if key1 not in self.__symbTab and key2 not in self.__symbTab:
            _a = self.__find_fact(key1)
            _b = self.__find_fact(key2)
            self.__negation[key1] = key2
            self.__negation[key2] = key1
            return self.__check_consistancy(key1, key2)
        # 2 existent
        if key1 in self.__symbTab and key2 in self.__symbTab:
            if key1 in self.__negation or key2 in self.__negation:
                return 0
            # gestion conflit
            _fa = self.__symbTab[key1]
            _fb = self.__symbTab[key2]
            if _fa.discret() * _fb.discret() == 1: return 0
            if abs(_fa.valeur) > abs(_fb.valeur):
                _fb.valeur = - _fa.valeur
            elif abs(_fb.valeur) > abs(_fa.valeur):
                _fa.valeur = - _fb.valeur
            elif _fa.discret() == _fb.discret():
                _fa.valeur = _fb.valeur = 0
            self.__negation[key1] = key2
            self.__negation[key2] = key1
            return self.__check_consistancy(key1, key2)
        # 1 existe
        if key1 in self.__symbTab:
            if key1 in self.__negation: return -1
            _f = self.__find_fact(key2)
            _f.valeur = - self.__symbTab[key1].valeur
            self.__negation[key1] = key2
            self.__negation[key2] = key1
            return self.__check_consistancy(key1, key2)
        if key2 in self.__symbTab:
            if key2 in self.__negation: return -1
            _f = self.__find_fact(key1)
            _f.valeur = - self.__symbTab[key2].valeur
            self.__negation[key1] = key2
            self.__negation[key2] = key1
            return self.__check_consistancy(key1, key2)

    def __updateNot(self, keysymb:str) -> None:
        """ helper for opposed values """
        _not = self.get_opposition(keysymb)
        if _not:
            self.__symbTab[_not].valeur = - self.__symbTab[keysymb].valeur

    def get_opposition(self, keysymb:str) -> str:
        """ find opposition if there is, else None """
        return self.__negation.get(keysymb, None)
    
    #=========== facts key <-> idnum ==================#
    
    def get_idnumFact(self, key:str) -> int:
        """ find idnum from userid """
        _fact = self.get_userFact(key)
        if _fact is None: return -1
        return self.__symbTab[key].idnum
    def get_useridFact(self, idnum:int) -> str:
        """ find the userid from idnum """
        return self.__reverseSym.get(idnum, None)
    def get_userFact(self, key:str) -> Fait:
        """ access to some fact in the symbTab """
        return self.__symbTab.get(key, None)
        
    #============ goals ================================#
    def add_goal(self, keysymb:str) -> bool:
        """
           False if fact not in table
           False if fact not prouvable
           True otherwise (added to goals)
        """
        _f = self.get_userFact(keysymb)
        if _f is None or not _f.prouvable: return False
        self.del_knowledge(keysymb)
        self.__query.add(keysymb)
        _okey = self.get_opposition(keysymb)
        if _okey is not None:
            self.del_knowledge(_okey)
            self.__query.add(_okey)
            
        return True

    def del_goal(self, keysymb:str) -> None:
        """
            if keysymb in goals, throw it away
        """
        _okey = self.get_opposition(keysymb)
        self.__query.discard(keysymb)
        self.__query.discard(_okey) # even None can be discarded

    def reset_goal(self) -> None:
        """
           flush goals
        """
        self.__query.clear()

    def get_goals(self) -> list:
        """ needed for local failure """
        return list(self.__query)
    #==================== résolution ======================================#
    @property
    def inconsistance(self):
        """ flag for inconsistency """
        return self.__inconsistance
    @inconsistance.setter
    def inconsistance(self, v):
        """ set a boolean to inconstency flag """
        self.__inconsistance = bool(v)
    
    def get_evalLeft(self, left:set) -> 'Number':
        """ a set of int => a value """
        return min([self.get_userFact(_).discret() 
                    for _ in self.get_useridList(left)])
    
    def get_useridList(self, fset: set) -> list:
        """ from a set of int find a list of userid """
        return [ self.get_useridFact(_) for _ in fset ]
            
    def resolution(self, reg_mod:int, memory:bool) -> tuple:
        """ 3 régimes, 2 modes
            memory: True on se rappelle les règles

            :return: nb règles + success/failure
            print nb_call regle
            print nb new facts
            print stop's reasons
        """
        if reg_mod > 2:
            raise ValueError("This 'mini-kernel' do not provide "
                             "the mode {}".format(reg_mod))
        self.inconsistance = False
        _reg = "fw bw mix".split()
        _mod = "dfs bfs".split()
        if reg_mod in range(6):
            _0 = _reg[int(reg_mod/2)] # 0|1 -> 0, 2|3 -> 1, 3|4 -> 2
            _1 = _mod[reg_mod % 2] # odd -> 1, even -> 0
            _meth = "_{}__{}_{}".format('Calcul', _0, _1)
            return getattr(self, _meth)(memory)

    @staticmethod
    def res_summary(count:dict, facts:list,
                    goals:list, rules:list,
                    memory:set, struct:str,
                    meth:str, diag:Diagnostic) -> str:
        """ Factorization of the summary at the end of resolution """

        _str = "{0} {1} {0}\n".format("-"*7, "Summary {}".format(meth))
        _len = len(_str)
        _str += ("compteurs de règles exploitées\n>>> {}, total = {}\n"
                "".format(count, sum(count.values())))
        _str += "nouveaux faits établis\n>>> {}\n".format(facts)
        _str += "buts restant à établir\n>>> {}\n".format(goals)
        _deb = "=== ordre de déclenchement ==="
        _end = "="*len(_deb)+"\n"
        _str += "{}\n{}{}\n".format(_deb, diag, _end)
        _0 = "Règles à essayer dans la {} : {}"
        _1 = ', '.join([str(r.idnum) for r in rules])
        _str += _0.format(struct, _1 if _1 != '' else []) + "\n"
        _str += "mémoire {} total {}\n".format(memory, len(memory))
        _str += "{}".format('-'*_len)

        return _str

    def __fw_dfs(self, memory:bool) -> tuple:
        """ chaînage avant en profondeur d'abord """
        _count = {}
        _mem = set()
        _newFacts = []
        _nbRules = 0
        _todo = self.selectableRules()
        self.__diag.clear()
        _saturation = len(self.__query) == 0
        _fini = (_todo == [] if _saturation
                            else len(self.__query) == 0)
        _iter = 0 ; _changed = True

        #================ le code ================================#
        while not _fini:
            if _changed:
                _iter += 1
                print("Itération {:02d}".format(_iter), end = ': ')
            _changed = False
            print("Pile des règles à traiter", [r.idnum for r in _todo])
            if _todo == []: _fini = True ; continue
            _r = _todo.pop(0)
            if _r.idnum in _mem:
                # mode monotomne, une règle déjà déclenchée n'ajoute rien
                print("Rule {} already applied, ignore it".format(_r.idnum))
                continue
            _nbRules += 1 # compteur de règles déclenchées
            print(">> Trigger R{:02d}".format(_r.idnum), end=' .. ')
            _v = self.get_evalLeft(_r.gauche)
            # on sait qu'il n'y a qu'un seul membre droit
            _oname = self.get_useridList(_r.droite)[0]
            if _v == 1: # la règle est utilisée
                print("success")
                self.__diag.add(_r.idnum, _oname, _v)
                _count[_r.idnum] = _count.get(_r.idnum, 0) +1
                if memory:
                    print(">>> Memorizing Rule {}".format(_r.idnum))
                    _mem.add(_r.idnum)
                if self.check_knowledge(_oname):
                    print("Updating information")
                    _add = False
                else:
                    print("New Fact", _oname)
                    _add = True
                    self.add_knowledge(_oname)
                _old = self.get_userFact(_oname).discret()
                if _old == 0:
                    print('update value for', _oname)
                    # maj -> comme si nouveau
                    if not _add: _add = True
                elif _old == -1:
                    print("fw_dfs: Erreur !!!! Pb with", _oname)
                    self.__inconsistance = True
                    return _nbRules, False
                else:
                    print("Value is already set for", _oname)
                if _add: # on fait le travail demandé 
                    # un nouveau fait est "connu" -> règles
                    _newFacts.append(_oname)
                    _changed = True
                    self.change_knowledge(_oname, _v)
                    for x in self.selectableRules()[::-1]:
                        _todo.insert(0, x)

            else:
                self.__diag.add_failure(_r.idnum, _oname)
                print("failure")
                
            _fini = (_todo == [] if _saturation
                                    else len(self.__query) == 0)

        #=============== diagnostic ==============================#
        _sum = self.res_summary(_count, _newFacts, self.get_goals(),
                                _todo, _mem, "pile", "fw_dfs",
                                self.__diag)
        print(_sum)
        #===================== return ============================#
        return _nbRules, (_newFacts != [] if _saturation
                          else len(self.__query) == 0)

    def __one_lvl(self, _todo:list, memory:bool) -> list:
        """ all candidates rules are used at once 
            the facts collected are processed outside
        """
        print("File des règles à traiter", [r.idnum for r in _todo])
        _foundFacts = []
        for rule in _todo:
            if rule.idnum in self.__mem:
                print("Rule {} already applied, ignore it".format(rule.idnum))
                continue
            print(">>> Trigger R{:02}".format(rule.idnum),
                  end = ' .. ')
            self.__nbRules += 1
            self.__count[rule.idnum] = self.__count.get(rule.idnum, 0)+1
            _v = self.get_evalLeft(rule.gauche)
            _oname = self.get_useridList(rule.droite)[0]
            if _v == 1: # Règle utilisée
                self.__diag.add(rule.idnum, _oname, _v)
                if memory:
                    print("success\n>>> Memorizing Rule {}".format(rule.idnum))
                    self.__mem.add(rule.idnum)
                else: print("success")
                _foundFacts.append(_oname)
            else:
                self.__diag.add_failure(rule.idnum, _oname)
                print("failure")
        return _foundFacts

    def __fw_bfs(self, memory:bool) -> tuple:
        """ chainage avant en largeur d'abord 
            on fait le parcours horizontal, on collecte les faits
            on lance un seul selectRules
        """
        self.__count = {}
        self.__mem = set()
        _newFacts = []
        self.__nbRules = 0
        self.__diag.clear()
        _todo = self.selectableRules()
        _changed = True
        _saturation = len(self.__query) == 0
        _fini = (_todo == [] if _saturation
                            else len(self.__query) == 0)

        #================ le code ================================#
        _cycle = 0
        while _changed and not _fini:
            _cycle += 1
            print("#{0} Début cycle {1:02d} {0}#".format('-'*7, _cycle))
            _ = self.__one_lvl(_todo, memory)
            _changed = False
            for _oname in _: # traitement des informations
                _add = False
                if not self.check_knowledge(_oname):
                    _changed = True
                    _add = True
                    _newFacts.append(_oname)
                    self.add_knowledge(_oname)
                else: _add = False
                _old = self.get_userFact(_oname).discret()
                if _old == 0:
                    print('update value for', _oname)
                    self.change_knowledge(_oname, 1)
                    # maj -> comme si nouveau
                    _changed = True
                    if not _add : _newFacts.append(_oname)
                elif _old == -1:
                    print("fw_bfs: Erreur !!!! Pb with", _oname)
                    self.__inconsistance = True
                    return self.__nbRules, False
                else:
                    print("Value is already set for", _oname)

            _todo = self.selectableRules() if _changed else []
            _fini = (_todo == [] if _saturation
                            else len(self.__query) == 0)
                
                    
        #=============== diagnostic ==============================#
        _sum = self.res_summary(self.__count, _newFacts,
                                  self.get_goals(), 
                                  _todo, self.__mem, "file", "fw_bfs",
                                self.__diag)
        print(_sum)
        #===================== return ============================#
        return self.__nbRules, (_newFacts != [] if _saturation
                          else len(self.__query) == 0)

    def __bw_dfs(self, avecMem:bool) -> (int, bool):
        """ chainage arrière en profondeur d'abord """
        _targets = self.get_goals()
        _proof = {x:[] for x in (True, False)}
        # as lit and non-lit are bound we need to clean the mess
        # 1st split prouvable vs not prouvable
        for key in _targets:
            if self.get_userFact(key).prouvable:
                _proof[True].append(key)
            else:
                _proof[False].append(key)
                # peut-être que l'opposé sera utilisable
                # s'il n'existe pas, inutile de calculer,
                # le résultat est connu -> Faux
                if self.get_opposition(key) is None: return 0, False
                    
        print("<+> Initial goals {}".format(_targets))
        print("<+> Effective goals {}".format(_proof[True]))
        # autre initialisation
        self.__count = {}
        self.__mem = {}
        self.__diag.clear()
        self.__nbR = 0
        #================ le code ================================#
        _success = self.__noeudET(_proof[True][:], 0, [], avecMem)
        #=============== diagnostic ==============================#
        _sum = self.res_summary(self.__count, [], _proof[True],
                                  [], self.__mem, "pile", "bw_dfs",
                                self.__diag)
        print(_sum)
        #===================== return ============================#
        return self.__nbR, _success

    def __noeudET(self, buts:list, nbRegles:int,
                  branch:list, avecMem:bool) -> bool:
        """ un noeud ET échoue si l'un des buts échoue """
        if __debug__:
            print("{} buts {}, pf = {}"
                  "".format('*'*nbRegles, buts, nbRegles))
            
        if buts == [] : return True
        elif self.__noeudOU(buts[0], nbRegles, branch, avecMem):
            return self.__noeudET(buts[1:], nbRegles, branch, avecMem)
        else: return False

    def __noeudOU(self, goal:str, nbRegles:int, branch, avecMem:bool) -> bool:
        """
        On regarde si le but est dans la base 
        Sinon on regarde les regles possibles
        """
        if self.check_knowledge(goal):
            if __debug__: print("{} is knowledge".format(goal))
            return self.get_userFact(goal).discret() == 1 # known fact
        if avecMem and goal in self.__mem:
            if __debug__: print("{} already evaluated".format(goal))
            return self.__mem[goal]
        if nbRegles >= len(self.__rules):
            if __debug__: print("Loop detected, processus aborted")
            return False # loop detection
        success = False
        aTester = [self.__rules[x] for x in self.get_userFact(goal).droite]
        while not success and aTester != []:
            r = aTester.pop(0) # 1ere regle
            if avecMem and r.idnum in branch:
                if __debug__:
                    print("R{:02d} already used in {}"
                          "".format(r.idnum, branch))
                continue
            self.__nbR += 1
            if __debug__:
                print("{} Try R{:02d}, pf = {}, total = {}"
                    "".format('>'*(nbRegles+1),
                              r.idnum, nbRegles+1, self.__nbR))
            nG = [self.get_useridFact(x) for x in r.gauche]
            _nbr = branch[:]
            _nbr.append(r.idnum)
            success = self.__noeudET(nG, nbRegles+1, _nbr, avecMem)
            if avecMem: self.__mem[goal] = success
            if __debug__:
                print("{} R{:02d} at pf = {}"
                      "".format("success" if success else "failed",
                                r.idnum, nbRegles+1))
            if success: self.__diag.add(r.idnum, goal, 1)
            else: self.__diag.add_failure(r.idnum, goal)

        return success
    
    #=================== display ==========================================#
    def show(self) -> None:
        """
           display the symbtab's content
        """
        for k in self.__symbTab:
            _f = self.__symbTab[k]
            print(k, "gauche {0.gauche}, droite {0.droite}".format(_f))

    #==================== pick rules of interest =========================#
    def selectableRules(self) -> list:
        """ ordered list if Regle.gauche is in base """
        _known = set([self.get_idnumFact(x) for x in self.__base])
        return [r for r in self.__rules if r.gauche.issubset(_known) ]

    def selectableProofs(self) -> list:
        """ ordered list if Regle.droite is in goals """
        _goals = set([self.get_idnumFact(x) for x in self.__query])
        return [r for r in self.__rules if r.droite.issubset(_goals) ]

    def __selectableQueries(self, rid:int) -> set:
        """ helper to select rules 
            if one prouvable lit has discret <= 0: cancel 
        """
        r = self.__rules[rid]
        _store = set()
        _candidates = self.get_askableFacts()
        for idnum in r.gauche:
            _k = self.get_useridFact(idnum)
            if self.is_negative(_k): #no question on negative lit
                _k = self.get_opposition(_k)
                if _k is None: continue
            _f = self.get_userFact(_k)
            if _f.discret() < 0: return set()
            if _f.prouvable and _f.discret() <= 0:
                return set()
            if _k in _candidates and _f.discret() == 0:
                _store.add(_k)
        return frozenset(_store)
    
    def selectableQueries(self) -> list:
        """ return tuple rid, set(userid for query) """
        return [ (r.idnum, self.__selectableQueries(r.idnum))
                 for r in self.__rules ]

    def __buildContraposee(self, rid:int) -> str:
        """ helper for contraposée """
        r = self.__rules[rid]
        if len(r.gauche) != 1 or len(r.droite) != 1: return None
        if r.fiabilite != 1: return None
        _g = self.get_useridList(r.gauche)[0]
        _d = self.get_useridList(r.droite)[0]
        if (self.get_userFact(_d).discret() == -1
            and
            self.get_userFact(_g).discret() == 0):
            return "{} -> {}".format(self.get_opposed_lit(_d),
                                     self.get_opposed_lit(_g))
    def selectableContra(self) -> list:
        """ return tuples rid, None or rid, rule """
        return [ (r.idnum, self.__buildContraposee(r.idnum))
                 for r in self.__rules ]

    def __selectableNeg(self, rid:int) -> set:
        """ this is only for atoms with prefix in self.__neg """
        r = self.__rules[rid]
        _store = set()
        for idnum in r.gauche:
            _k = self.get_useridFact(idnum)
            _f = self.get_userFact(_k)
            if _f.discret() < 0: return set()
            if (self.is_positive(_k) and _f.discret() == 0):
                return set()
            if self.is_negative(_k) and _f.discret() == 0:
                _store.add(self.get_opposed_lit(_k))
        return frozenset(_store)
        
    def selectableNegation(self) -> list:
        """ return tuples rid, set of positive lit """
        return [ (r.idnum, self.__selectableNeg(r.idnum))
                 for r in self.__rules ]

    #========================== some helpers =============================#
    def get_askableFacts(self) -> list:
        """ askable : if Im not prouvable and my bounded neither """
        def localCond(x):
            """ shorthand for condition required """
            y = self.get_opposition(x)
            return (self.is_positive(x) and
                    not self.__symbTab[x].prouvable and
                    (y is None or
                     not self.__symbTab[y].prouvable))
        return [x for x in self.__symbTab if localCond(x)]

    def get_askableWithRules(self) -> dict:
        """ provides for each askable the rules impacted """
        def localSet(x):
            """ both fact and bounded if there is one """
            y = self.get_opposition(x)
            _set = frozenset(self.__symbTab[x].gauche)
            return (_set if y is None
                    else _set.union(self.__symbTab[y].gauche))
        return {x: localSet(x) for x in self.get_askableFacts()}
    #============================== properties ============================#
    #======================= views on internal struct =====================#
    
    @property
    def table(self):
        """ a view of __symbTab """
        return [ (x[0], repr(x[1])) for x in self.__symbTab.items() ]
    @property
    def rules(self):
        """ a view of __rules """
        return [ repr(x) for x in self.__rules ]
    @property
    def base(self):
        """ a view of __base """
        return [ repr(self.__symbTab[x]) for x in self.__base ]

    @property
    def goals(self):
        """ a view of __query """
        return [ repr(self.__symbTab[x]) for x in self.__query ]

    #=================== littéraux ========================================#
    def get_positive_idnum(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([x.idnum for x in self.get_positiveFact()])
    def get_negative_idnum(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([x.idnum for x in self.get_negativeFact()])

    def get_positiveFact(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([self.__symbTab[x]
                          for x in self.get_positive_userid()])
    def get_negativeFact(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([self.__symbTab[x] 
                          for x in self.get_negative_userid()])
    
    def get_positive_userid(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([x for x in self.__symbTab
                          if not any([x.startswith(pref)
                                      for pref in self.__neg])])
    def get_negative_userid(self) -> set:
        """ non- not- pas- are negative """
        return frozenset([x for x in self.__symbTab
                          if any([x.startswith(pref)
                                      for pref in self.__neg])])

    def is_negative(self, key:str) -> bool:
        """ negative if exists and starts with the right prefix 
            be cautious: costly
        """
        return key in self.get_negative_userid()

    def is_positive(self, key:str) -> bool:
        """ positive if exists and does not start with the right prefix 
            be cautious: costly
        """
        return key in self.get_positive_userid()
    
    def __find_opposed_userid(self) -> set:
        """ non- not- pas- are negative helper pour build_opposition """
        # if no opposition -> create non-x
        _pos = [x for x in self.get_positive_userid()
                if self.get_opposition(x) is None]
        _neg = [x[4:] for x in [y for y in self.get_negative_userid()
                                if self.get_opposition(y) is None]]

        _uniquepos = frozenset(_pos).difference(_neg)
        for key in _uniquepos: self.__find_fact('non-'+key)
        _uniqueneg = frozenset(_neg).difference(_pos)
        for key in _uniqueneg: self.__find_fact(key)
        return frozenset([(x[4:], x) for x in self.get_negative_userid()])

    def build_opposition(self) -> bool:
        """ make opposition real """
        _ok = True
        for x, y in self.__find_opposed_userid():
            _ = self.add_opposition(x, y)
            if _ != 1:
                print("Trouble for add_opposition({}, {}) -> {}"
                      "".format(x, y, _))
                _ok = False
        return _ok

    def get_opposed_lit(self, key:str) -> str:
        """ given some key find the opposed one if exists
            else: build the key
        """
        _newkey = self.get_opposition(key)
        if _newkey is None:
            _negatif = key[:4] in self.__neg # bool
            _newkey = key[4:] if _negatif else 'non-'+key
            self.add_opposition(key, _newkey)
        return _newkey
    

if __name__ == "__main__":
    c = Calcul()
    c.add_regle("a & non-b -> c")
    c.add_regle("e & non-c -> b")
    c.add_regle("d -> non-a")
    c.add_regle("d & e -> f")
    c.add_regle("x -> y")
    c.add_regle("w -> z")
    c.add_regle("A -> B")
    c.add_regle("C -> D")
    for lit in "aex":
        c.add_knowledge(lit)
        c.change_knowledge(lit, 1)
    # pièges pour négations et questions
    c.add_opposition('x', 'z')
    c.add_opposition('A', 'D')
    c.add_opposition('B', 'C')
    c.add_knowledge('B')
    c.change_knowledge('B', -1)
    c.build_opposition()
    keys = "Queries Contra Negation".split()
    for k in keys:
        print("#{0} {1} {0}#".format("="*7, k))
        print(getattr(c, "selectable{}".format(k))())
    print("="*23)
    print("les faits interrogeables sont {}".format(c.get_askableFacts()))
