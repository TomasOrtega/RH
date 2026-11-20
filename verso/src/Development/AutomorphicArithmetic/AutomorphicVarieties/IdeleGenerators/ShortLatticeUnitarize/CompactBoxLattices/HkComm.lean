import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use extensionality with `i j : 2`. Conclude with `FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)`.
-/
private theorem ext_loc {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

/- English proof (translation)
Use `ext_loc fun x => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `hx : x = w`. Substitute `hx` using the available equality. Rewrite using `[hk, mul_one, one_mul]`.

Rewrite using `[pLoc_locGL_of_ne hx, mul_one, one_mul]`.
-/
private theorem comm_of_triv {w : Pl F} (g : GL (Fin 2) (w.adicCompletion F)) {k : GL (Fin 2) (Af F)}
    (hk : Matrix.GeneralLinearGroup.map (pLoc F w) k = 1) : k * locGL F 2 w g = locGL F 2 w g * k := by
  refine ext_loc fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = w
  · subst hx; rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

/- English proof (translation)
Introduce `k hk` and use `hx _ ((hK F).2.2.2.2.2 c w k hk)`.
-/
private theorem fix_loc (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
  fun k hk => hx _ ((hK F).2.2.2.2.2 c w k hk)

/- English proof (translation)
Take `⟨N, a, -, ha⟩` from `hR F w (c w)`. Take `⟨h1, h2⟩` from `ha V _ x (fix_loc hK ρ c hx w)`. Introduce `k hk`. Establish `hkw : Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)` using `(Subgroup.mem_iInf.1 hk) w`. Use `set kw := Matrix.GeneralLinearGroup.map (pLoc F w) k with hkwe`.

Establish `hm : k * (locGL F 2 w kw)⁻¹ ∈ Kc c` using `mul_mem hk (inv_mem ((hK F).2.2.2.2.2 c w kw hkw))`. Establish `ht : Matrix.GeneralLinearGroup.map (pLoc F w) (k * (locGL F 2 w kw)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, pLoc_locGL, ← hkwe, mul_inv_cancel]`. Establish `e : k = k * (locGL F 2 w kw)⁻¹ * locGL F 2 w kw` using `by rw [inv_mul_cancel_right]`. Establish `h3 : ρ (locGL F 2 w kw) (Uop w (ρ.comp (locGL F 2 w)) (c w) x) = Uop w (ρ.comp (locGL F 2 w)) (c w) x` using `h1 kw hkw`.

Establish `h4 : ρ (k * (locGL F 2 w kw)⁻¹) x = x` using `hx _ hm`. Rewrite using `[e, map_mul, Module.End.mul_apply, h3, h2, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ _ (ρ (locGL F 2 w (a i)) x) = ρ (locGL F 2 w (a i)) x`. Rewrite using `[← Module.End.mul_apply, ← map_mul, comm_of_triv _ ht, map_mul, Module.End.mul_apply, h4]`.
-/
private theorem uop_mem (hR : HkReps) (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) := by
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨h1, h2⟩ := ha V _ x (fix_loc hK ρ c hx w)
  intro k hk
  have hkw : Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := (Subgroup.mem_iInf.1 hk) w
  set kw := Matrix.GeneralLinearGroup.map (pLoc F w) k with hkwe
  have hm : k * (locGL F 2 w kw)⁻¹ ∈ Kc c := mul_mem hk (inv_mem ((hK F).2.2.2.2.2 c w kw hkw))
  have ht : Matrix.GeneralLinearGroup.map (pLoc F w) (k * (locGL F 2 w kw)⁻¹) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, ← hkwe, mul_inv_cancel]
  have e : k = k * (locGL F 2 w kw)⁻¹ * locGL F 2 w kw := by rw [inv_mul_cancel_right]
  have h3 : ρ (locGL F 2 w kw) (Uop w (ρ.comp (locGL F 2 w)) (c w) x) = Uop w (ρ.comp (locGL F 2 w)) (c w) x := h1 kw hkw
  have h4 : ρ (k * (locGL F 2 w kw)⁻¹) x = x := hx _ hm
  rw [e, map_mul, Module.End.mul_apply, h3, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ρ _ (ρ (locGL F 2 w (a i)) x) = ρ (locGL F 2 w (a i)) x
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv _ ht, map_mul, Module.End.mul_apply, h4]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
/- English proof (translation)
Introduce `hR hK F _ _ V _ _ ρ c x hx w`. Use `⟨uop_mem hR hK ρ c hx w, fun w' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w' = w`. Substitute `hw` using the available equality. Both sides reduce to the same expression.

Take `⟨N, a, -, ha⟩` from `hR F w (c w)`. Take `⟨N', a', -, ha'⟩` from `hR F w' (c w')`. Rewrite using `[(ha V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w') w)).2, (ha' V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w) w')).2, (ha V _ _ (fix_loc hK ρ c hx w)).2, (ha' V _ _ (fix_loc hK ρ c hx w')).2]`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ (locGL F 2 w (a i)) (ρ (locGL F 2 w' (a' j)) x) = ρ (locGL F 2 w' (a' j)) (ρ (locGL F 2 w (a i)) x)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, comm_of_triv (a' j) (pLoc_locGL_of_ne hw (a i)), map_mul, Module.End.mul_apply]`.
-/
theorem UpperTheory.V.Sd.Wc.hkComm :
    UpperTheory.V.Sd.Wc.HkReps → UpperTheory.V.Sd.Wc.KcTop → UpperTheory.V.Sd.Wc.HkComm := by
  intro hR hK F _ _ V _ _ ρ c x hx w
  refine ⟨uop_mem hR hK ρ c hx w, fun w' => ?_⟩
  by_cases hw : w' = w
  · subst hw; rfl
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨N', a', -, ha'⟩ := hR F w' (c w')
  rw [(ha V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w') w)).2, (ha' V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w) w')).2,
    (ha V _ _ (fix_loc hK ρ c hx w)).2, (ha' V _ _ (fix_loc hK ρ c hx w')).2]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change ρ (locGL F 2 w (a i)) (ρ (locGL F 2 w' (a' j)) x) = ρ (locGL F 2 w' (a' j)) (ρ (locGL F 2 w (a i)) x)
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv (a' j) (pLoc_locGL_of_ne hw (a i)), map_mul, Module.End.mul_apply]
