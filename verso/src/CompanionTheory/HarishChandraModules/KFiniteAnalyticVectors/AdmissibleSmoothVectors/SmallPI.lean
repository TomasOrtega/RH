import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly

noncomputable section

namespace CompanionTheory.D.gk.admitted

/- English proof (translation)
Establish `hdep : ¬ LinearIndependent ℂ b` using `fun h => by`. Use `h.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `h` using `(MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep`.

Rewrite `h` using `[MultilinearMap.alternatization_apply]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def, zsmul_eq_mul]`.
-/
theorem std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ} (hM : Module.finrank ℂ A < M)
    (b : Fin M → A) :
    ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : A) * (List.ofFn fun i => b (π i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def, zsmul_eq_mul]

/- English proof (translation)
Introduce `V _ _ W Y _ hYW E hE M hM a ha w hw`. Set `b : Fin M → Module.End ℂ Y` to `fun i => (E * a i).restrict (p := Y) (q := Y) fun y hy => hE _ (ha i y (hYW hy))`. Establish `hb : ∀ l : List (Fin M), word E (l.map a) w = (((l.map b).prod ⟨E w, hE w hw⟩ : Y) : V)`. Introduce `l`. Proceed by induction on `l with`.

Consider the case `nil => rfl`. Consider the case `cons i l ih`. Rewrite using `[List.map_cons, word_cons, Module.End.mul_apply, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]`. Both sides reduce to the same expression. Establish `hdim : Module.finrank ℂ (Module.End ℂ Y) < M`.

Rewrite using `[Module.finrank_linearMap, ← sq]`. Conclude with `hM`. Establish `h0` using `congrArg (fun T : Module.End ℂ Y => ((T ⟨E w, hE w hw⟩ : Y) : V)) (std_eq_zero hdim b)`. Simplify using `only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.zero_apply, Submodule.coe_zero] at h0`. Rewrite using `[← h0, stdPoly, LinearMap.sum_apply]`.

Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Establish `e1 : (List.ofFn fun i => a (π i)) = (List.ofFn π).map a` using `by rw [List.map_ofFn]; rfl`. Establish `e2 : (List.ofFn fun i => b (π i)) = (List.ofFn π).map b` using `by rw [List.map_ofFn]; rfl`. Rewrite using `[e1, e2, Module.End.mul_apply, Module.End.mul_apply, hb, Module.End.intCast_apply, Module.End.intCast_apply, Submodule.coe_smul_of_tower]`.
-/
theorem small_irreducible_representation : SmallPI := by
  intro V _ _ W Y _ hYW E hE M hM a ha w hw
  let b : Fin M → Module.End ℂ Y := fun i =>
    (E * a i).restrict (p := Y) (q := Y) fun y hy => hE _ (ha i y (hYW hy))
  have hb : ∀ l : List (Fin M), word E (l.map a) w = (((l.map b).prod ⟨E w, hE w hw⟩ : Y) : V) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.map_cons, word_cons, Module.End.mul_apply, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rfl
  have hdim : Module.finrank ℂ (Module.End ℂ Y) < M := by
    rw [Module.finrank_linearMap, ← sq]; exact hM
  have h0 := congrArg (fun T : Module.End ℂ Y => ((T ⟨E w, hE w hw⟩ : Y) : V)) (std_eq_zero hdim b)
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.zero_apply, Submodule.coe_zero] at h0
  rw [← h0, stdPoly, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e1 : (List.ofFn fun i => a (π i)) = (List.ofFn π).map a := by rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i => b (π i)) = (List.ofFn π).map b := by rw [List.map_ofFn]; rfl
  rw [e1, e2, Module.End.mul_apply, Module.End.mul_apply, hb, Module.End.intCast_apply, Module.End.intCast_apply,
    Submodule.coe_smul_of_tower]

end CompanionTheory.D.gk.admitted
