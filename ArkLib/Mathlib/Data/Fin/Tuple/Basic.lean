import Mathlib.Data.Fin.Tuple.Basic

lemma append_mk_lt {α} {m n : ℕ} (u : Fin m → α) (v : Fin n → α)
    (j : ℕ) (h : j < m + n) (hlt : j < m) :
    Fin.append u v ⟨j, h⟩ = u ⟨j, hlt⟩ := by
  rw [show (⟨j, h⟩ : Fin (m + n)) = Fin.castAdd n ⟨j, hlt⟩ from Fin.ext rfl, Fin.append_left]
