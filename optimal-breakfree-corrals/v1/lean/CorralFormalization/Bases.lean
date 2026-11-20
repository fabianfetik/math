import CorralFormalization.Basic

namespace CorralFormalization

/-- A finite lookup function used to state the height-three base. -/
def table5 (a0 a1 a2 a3 a4 : Fin 5) (j : Fin 5) : Fin 5 :=
  if j.val = 0 then a0 else
  if j.val = 1 then a1 else
  if j.val = 2 then a2 else
  if j.val = 3 then a3 else a4

def base3Perm0 : Equiv.Perm (Fin 5) := Equiv.refl (Fin 5)

noncomputable def base3Perm1 : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (table5 3 0 1 2 4) (by decide)

noncomputable def base3Perm2 : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (table5 2 1 4 0 3) (by decide)

theorem optimal_base_height_one : OriginalCorral 1 1 := by
  refine ⟨fun _ => Equiv.refl (Fin 1), fun _ => 0, ?_⟩
  intro a b hab
  have ha : a.1 = b.1 := Subsingleton.elim _ _
  have hb : a.2 = b.2 := Subsingleton.elim _ _
  exact Prod.ext ha hb

theorem optimal_base_height_three : OriginalCorral 3 5 := by
  refine ⟨(fun i => if i.val = 0 then base3Perm0 else
                    if i.val = 1 then base3Perm1 else base3Perm2),
          (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else 2), ?_⟩
  decide

/-- A finite lookup function used to state the height-five base. -/
def table9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Fin 9) (j : Fin 9) : Fin 9 :=
  if j.val = 0 then a0 else
  if j.val = 1 then a1 else
  if j.val = 2 then a2 else
  if j.val = 3 then a3 else
  if j.val = 4 then a4 else
  if j.val = 5 then a5 else
  if j.val = 6 then a6 else
  if j.val = 7 then a7 else a8

noncomputable def base5Perm0 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective (table9 8 5 3 4 7 1 0 6 2) (by decide)

noncomputable def base5Perm1 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective (table9 1 0 8 5 3 4 6 2 7) (by decide)

noncomputable def base5Perm2 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective (table9 7 1 0 8 5 3 6 2 4) (by decide)

noncomputable def base5Perm3 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective (table9 3 4 7 1 0 8 5 2 6) (by decide)

noncomputable def base5Perm4 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective (table9 5 3 4 7 1 0 8 6 2) (by decide)

theorem optimal_base_height_five : OriginalCorral 5 9 := by
  refine ⟨(fun i =>
            if i.val = 0 then base5Perm0 else
            if i.val = 1 then base5Perm1 else
            if i.val = 2 then base5Perm2 else
            if i.val = 3 then base5Perm3 else base5Perm4),
          (fun i =>
            if i.val = 0 then 0 else
            if i.val = 1 then 4 else
            if i.val = 2 then 3 else
            if i.val = 3 then 1 else 2), ?_⟩
  decide

end CorralFormalization
