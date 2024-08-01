#from abc import ABC, abstractmethod
#from math import prod
#from typing import Iterator

from sage.rings.infinity import PlusInfinity , MinusInfinity
from sage.rings.integer_ring import ZZ
#from sage.combinat.partition import Partitions
#from sage.combinat.permutation import Arrangements
#from sage.combinat.root_system.weyl_characters import WeylCharacterRing
#from sage.combinat.sf.sf import SymmetricFunctions
#from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from homogeneous import *


class LefschetzCollection (object) :

    def __contains__ ( self ) -> bool :
        raise NotImplementedError()        

    def __init__ ( self , starting_block: tuple[BundleBWB] , twists: tuple[BundleBWB] , support  ) -> None :
        self._base_space = None
        self._starting_block = []
        assert isinstance( starting_block , tuple ) , "The starting block needs to be given as tuple."        
        for index , bundle in enumerate(starting_block) :
            assert isinstance( bundle , BundleBWB ) , "The {i}-th bundle in the starting block needs to be a homogeneous bundle in BWB-format.".format(i=index)
            if index == 0 :
                self._base_space = bundle._base_space
            else :
                assert bundle._base_space == self._base_space , "The {i}-th bundle in the starting block does not live over the common base space of the previous bundle(s).".format(i=index)
            self._starting_block += [ bundle ]
        self._starting_block = tuple(self._starting_block)

        self._twists = []
        assert isinstance( twists , tuple ) , "The twists needs to be a given as tuple."        
        for index , twist in enumerate(twists) :
            assert isinstance( twist , BundleBWB ) , "The {i}-th twist needs to be a homogeneous bundle in BWB-format.".format(i=index)
            assert twist.is_line_bundle() , "The {i}-th twist needs to be a line bundle.".format(i=index)
            assert twist._base_space == self._base_space , "The {i}-th twist does not live over the common base space.".format(i=index)        
            self._twists += [ twist ]
        self._twists = tuple(self._twists)

        self._support = []
        assert isinstance( support , list ) , "The support needs to be a list."
        for point in support :
            for position , entry in enumerate(point) :
                if position == 0 :
                    assert entry in range(len(self._starting_block)) , "For a given support point, the first entry needs to be in the range from 0 to {l}.".format(l=len(self._starting_block))
                else :
                    assert entry in ZZ , "For a given support point, the entries need to be integers."
            self._support += [ point ]

        self._gram_matrix = None
        self._is_exceptional = None
        self._is_numerically_exceptional = None
        self._is_full = None

    def __iter__ ( self ) -> Iterator[ BundleBWB ] :
        raise NotImplementedError()
        
    def __len__ ( self ) -> int :
        return len(self._support)
        
    def __repr__ ( self ) -> tuple :
        return self._starting_block , self._twists , self._support
        
    def __str__ ( self ) -> str :
        return "Lefschetz collection {l} of over {bs}.".format(l=len(self),bs=self._base_space.as_string())

    def get_failing_semiorthogonal_relations ( self ) -> Iterator :
        raise NotImplementedError()        
        
    def gram_matrix ( self ) -> Matrix :
        raise NotImplementedError()        
        
    def is_exceptional ( self ) -> bool :
        raise NotImplementedError()
                
    def is_numerically_exceptional ( self ) -> bool :
        raise NotImplementedError()
        
