{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
module Main where

import Control.Monad.ST (RealWorld)
import Data.Unique.Tag (Tag, newTag)
import GHC.IO.Exception (IOErrorType (PermissionDenied))
import System.IO.Unsafe (unsafePerformIO)

------ ACTUAL IMPL -------------

class Schema g where
    data Relation g a b

data Relation2 a b = Relation2 (Tag RealWorld (a, b)) deriving (Eq, Ord)

------ EXAMPLE -----------------
data PeopleAndHobbies

data Person = Person {personName :: String}

data Activity = Activity {activityName :: String}

instance Schema PeopleAndHobbies where
    data Relation PeopleAndHobbies a b where
        Friend :: Relation PeopleAndHobbies Person Person
        Hobby :: Relation PeopleAndHobbies Person Activity
        Child :: Relation PeopleAndHobbies Person Person
        Spouse :: Relation PeopleAndHobbies Person Person

data Shae'sSchema

instance Schema Shae'sSchema where
    data Relation Shae'sSchema a b where
        ShaeHobby :: Relation Shae'sSchema Person Activity

friend :: Relation2 Person Person
friend = Relation2 (unsafePerformIO newTag)

main :: IO ()
main = return ()
