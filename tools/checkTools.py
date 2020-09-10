#!/usr/bin/python3
# -*- coding: utf-8 -*-
#

__author__ = "mmc <marc-michel dot corsini at u-bordeaux dot fr>"
__date__ = "24.01.19"
__usage__ = "some check_XXX Tools"
__update__ = "27.01.19 16:40"


import unittest
import sys

def check_property(prop:bool, msg:str='property is False',
                   letter:str='E') -> str:
    """ check that prop is fine """
    try:
        assert( prop ), '>>> failure: {}'.format(msg)
        _ = '.'
    except Exception as _e:
        import sys
        if sys.version_info[:2] >= (3, 3): print(_e, flush=True)
        else: print(_e)
        _ = letter
        
    return _
    
def check_attr(obj, att):
    """ un objet avec un attribut spécifique """
    if not hasattr(obj, att):
        raise unittest.SkipTest("{} missing for {}"
                                "".format(att, obj.__class__.__name__))

def check_ro(obj, latt, verbose=False):
    """ regarde si les attributs sont ro """
    _missing = []
    _rw = []
    for att in latt:
        if verbose: print(att, 'processing ...', flush=True)
        if not hasattr(obj, att):
            _missing.append(att) ; continue
        else:
            _old = getattr(obj, att)

        if hasattr(_old, '__iter__'):
            _x = 'mmc' if 'mmc' not in _old else 'capharnaumadlib'
        else: _x = 'mmc' if _old != 'mmc' else 42
        try:
            setattr(obj, att, _x)
            if getattr(obj, att) == _x:
                _rw.append(att) ; setattr(obj, att, _old) ; continue
        except:
            pass
        
        if hasattr(_old, '__len__'):
            _szold = len(_old)
            if isinstance(_old, list):
                try:
                    _old.append(_x)
                    if len(getattr(obj, att)) > _szold:
                        _rw.append(att) ; setattr(obj, att, _old[:-1])
                except: pass
            elif isinstance(_old, str):
                _old+str(_x)
                if len(getattr(obj, att)) > _szold:
                    _rw.append(att) ; setattr(obj, att, _old[:-len(str(_x))])
            elif isinstance(_old, set):
                try:
                    _old.add(_x)
                    if len(getattr(obj, att)) > _szold:
                        _rw.append(att) ; _old.discard(_x)
                except: pass
            elif isinstance(_old, dict):
                _old[_x] = _x
                if verbose: print('>>> ', _old.get(_x))
                _y = getattr(obj, att).get(_x, None)
                if (len(getattr(obj, att)) > _szold or
                     _y == _x) :
                    _rw.append(att)
                    del getattr(obj, att)[_x]

    return _missing, _rw

class Bidon:
    __slots__ = ('x', 'y', 'z', 't')
    def __init__(self, x=42):
        self.x = x
        self.y = [3]
        self.z = set([5])
        self.t = {'mmc': 42}

    @property
    def u(self): return frozenset(self.z)
    @property
    def v(self): return self.y[:]
    @property
    def w(self): return tuple(self.y)
    @property
    def a(self): return self.t.copy()
        
        
if __name__ == "__main__":
    print(check_property(Bidon().x == 42,
                         "pb with default parameter of Bidon", "X"))
    print(check_property(hasattr(Bidon(), 'b'),
                         "'Bidon' objects have no 'b' attribute,"
                         " result was expected"))
    print(check_ro(Bidon(), "x y z t u v w a".split(), True))
