module Testing where
open import Data.Nat.Base
open import Agda.Builtin.Int

n = 1
m = 1 + 1

_-'_ : ℕ → ℕ → ℕ
-- odšteje
n -' zero = negsuc n
n -' suc m = {!   !}
