import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ ι n A w h _hl r χ x hWD hType`. Take `⟨t, _ht, φ, hφ, N, a, hMon, hFS, hax⟩` from `hWD`. Take `⟨b, hbx, hbN, hbρ⟩` from `hType`. Establish `hiso : a.Iso b` using `WD.mk_eq_mk.mp (hax.trans hbx.symm)`. Take `⟨e, he1, he2⟩` from `hiso`.

Take `⟨_hNnil, U, hUo, hU⟩` from `hMon`. Take `⟨haN, hFS⟩` from `hFS`. Establish `htoEnd : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), toEndC ι X = Matrix.toLin' (X.map ι)` using `fun X => rfl`. Establish `haN0 : a.N = 0`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Establish `h0` using `he2 v`. Rewrite `h0` using `[hbN, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff]`. Conclude with `h0`. Establish `hN0 : N = 0`.

Establish `h0 : Matrix.toLin' (N.map ι) = Matrix.toLin' (0 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← htoEnd, ← haN, haN0, map_zero]`. Establish `h2` using `Matrix.toLin'.injective h0`. Use extensionality with `i j`. Establish `h3` using `congrFun (congrFun h2 i) j`.

Simplify using `using h3`. Establish `hpow : ∀ s : Ine (F` using `L) A, ∃ m : ℕ, 0 < m ∧ s ^ m ∈ U := by`. Introduce `s`. Establish `hUn : (U : Set (Ine (F` using `L) A)) ∈ nhds (1 : Ine (F := L) A) := hUo.mem_nhds U.one_mem`. Take `⟨u, hu, hsub⟩` from `(mem_nhds_subtype _ _ _).mp hUn`.

Take `⟨E, hEfin, hEu⟩` from `(krullTopology_mem_nhds_one_iff L Ω u).mp hu`. Set `f : ℕ → (E →ₐ[L] Ω)` to `fun k => ((s : G L Ω) ^ k).toAlgHom.comp E.val`. Take `⟨i, j, hij, hfij⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `key : ∀ i j : ℕ, i < j → f i = f j → s ^ (j - i) ∈ U`. Introduce `i j hlt hf`.

Apply `hsub` to reduce the goal to its premises. Apply `hEu` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Establish `hy'` using `congrArg (fun φ : E →ₐ[L] Ω => φ ⟨y, hy⟩) hf`.

Simplify using `only [f, AlgHom.comp_apply] at hy'`. Establish `hj : (s : G L Ω) ^ j = (s : G L Ω) ^ i * (s : G L Ω) ^ (j - i)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hlt.le]`. Rewrite `hy'` using `[hj]`. Establish `hy'' : ((s : G L Ω) ^ i) y = ((s : G L Ω) ^ i) (((s : G L Ω) ^ (j - i)) y)` using `hy'`.

Use `((s : G L Ω) ^ i).injective hy''` as an intermediate fact. Use `show ((s ^ (j - i) : Ine (F := L) A) : G L Ω) • y = y`. Rewrite using `[Subgroup.coe_pow]`. Conclude with `this.symm`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases.

Conclude with `⟨j - i, Nat.sub_pos_of_lt hlt, key i j hlt hfij⟩`. Conclude with `⟨i - j, Nat.sub_pos_of_lt hlt, key j i hlt hfij.symm⟩`. Establish `hrs : ∀ s : Ine (F` using `L) A, Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) = a.ρ (ineIncl h s) := by`. Introduce `s`. Take `⟨m, hm, hsm⟩` from `hpow s`.

Establish `hrm : (r (s : G L Ω)) ^ m = 1`. Apply `Units.ext` to reduce the goal to its premises. Establish `h1` using `hU _ hsm`. Rewrite `h1` using `[hN0, smul_zero, IsNilpotent.exp_zero]`. Rewrite using `[← map_pow, ← Subgroup.coe_pow, h1, Units.val_one]`.

Use `set f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) with hf`. Establish `hfm : f ^ m = 1`. Rewrite using `[hf, ← htoEnd, ← map_pow, ← Units.val_pow_eq_pow_val, hrm, Units.val_one, map_one]`. Establish `hfss : f.IsSemisimple`. Apply `Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ m - Polynomial.C 1)` to reduce the goal to its premises.

Conclude with `(Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree`. Simplify using `[hfm]`. Take `⟨hcomm, hnil⟩` from `hFS (ineIncl h s)`. Establish `hwd : toEndC ι (wdMat t hφ r N (ineIncl h s)) = f`. Simplify using `only [wdMat, hN0, smul_zero, IsNilpotent.exp_zero, mul_one]`.

Both sides reduce to the same expression. Simplify using `only [hwd] at hcomm hnil`. Establish `hss2 : (f - a.ρ (ineIncl h s)).IsSemisimple` using `hfss.sub_of_commute hcomm.symm (a.semisimple _)`. Conclude with `sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss2)`. Set `P : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' (e : Module.End ℂ (Fin n → ℂ))`.

Set `Pi : Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toMatrix' (e.symm : Module.End ℂ (Fin n → ℂ))`. Establish `hPPi : P * Pi = 1`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Rewrite using `[show (e : Module.End ℂ (Fin n → ℂ)).comp (e.symm : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from LinearMap.ext fun v => by simp]`. Conclude with `LinearMap.toMatrix'_id`.

Establish `hPiP : Pi * P = 1`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Rewrite using `[show (e.symm : Module.End ℂ (Fin n → ℂ)).comp (e : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from LinearMap.ext fun v => by simp]`. Conclude with `LinearMap.toMatrix'_id`. Set `Φ` to `ι.symm.toRingHom.mapMatrix (m := Fin n)`.

Set `g : GL (Fin n) (Qbar l)` to `⟨Φ P, Φ Pi, by rw [← map_mul, hPPi, map_one], by rw [← map_mul, hPiP, map_one]⟩`. Use `⟨g, fun s => ?_⟩` and prove the remaining obligations. Establish `hA : a.ρ (ineIncl h s) = (e.symm : Module.End ℂ (Fin n → ℂ)).comp ((b.ρ (ineIncl h s)).comp (e : Module.End ℂ (Fin n → ℂ)))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `[← he1]`. Establish `hR : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι = Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P`. Establish `h1` using `congrArg LinearMap.toMatrix' (hrs s)`. Rewrite `h1` using `[LinearMap.toMatrix'_toLin', hA, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hbρ s, LinearMap.toMatrix'_toLin', ← mul_assoc]`. Rewrite using `[h1]`.

Both sides reduce to the same expression. Establish `hback : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) = Φ ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι)`. Use extensionality with `i j`. Simplify using `[Φ]`. Use `show Φ P * (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * Φ Pi = _`.

Rewrite using `[hback, hR, ← map_mul, ← map_mul]`. Rewrite using `[show P * (Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P) * Pi = Matrix.diagonal (fun i => ι (χ i s : Qbar l)) by`. Rewrite using `[← mul_assoc, ← mul_assoc, hPPi, one_mul, mul_assoc, hPPi, mul_one]]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Φ]`. Simplify using `[Φ, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (r : G L Ω →* GL (Fin n) (Qbar l)) (χ : Fin n → Ine (F := L) A →* (Qbar l)ˣ) (x : WD h), IsWDOf ι r x → IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x → ∃ g : GL (Fin n) (Qbar l), ∀ t : Ine (F := L) A, ((g * r t * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (χ i t : Qbar l) := by
  intro l _ L Ω _ _ _ _ _ ι n A w h _hl r χ x hWD hType
  classical
  obtain ⟨t, _ht, φ, hφ, N, a, hMon, hFS, hax⟩ := hWD
  obtain ⟨b, hbx, hbN, hbρ⟩ := hType
  have hiso : a.Iso b := WD.mk_eq_mk.mp (hax.trans hbx.symm)
  obtain ⟨e, he1, he2⟩ := hiso
  obtain ⟨_hNnil, U, hUo, hU⟩ := hMon
  obtain ⟨haN, hFS⟩ := hFS
  have htoEnd : ∀ X : Matrix (Fin n) (Fin n) (Qbar l),
      toEndC ι X = Matrix.toLin' (X.map ι) := fun X => rfl
  have haN0 : a.N = 0 := by
    apply LinearMap.ext
    intro v
    have h0 := he2 v
    rw [hbN, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h0
    exact h0
  have hN0 : N = 0 := by
    have h0 : Matrix.toLin' (N.map ι) = Matrix.toLin' (0 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← htoEnd, ← haN, haN0, map_zero]
    have h2 := Matrix.toLin'.injective h0
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa using h3
  have hpow : ∀ s : Ine (F := L) A, ∃ m : ℕ, 0 < m ∧ s ^ m ∈ U := by
    intro s
    have hUn : (U : Set (Ine (F := L) A)) ∈ nhds (1 : Ine (F := L) A) := hUo.mem_nhds U.one_mem
    obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).mp hUn
    obtain ⟨E, hEfin, hEu⟩ := (krullTopology_mem_nhds_one_iff L Ω u).mp hu
    let f : ℕ → (E →ₐ[L] Ω) := fun k => ((s : G L Ω) ^ k).toAlgHom.comp E.val
    obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
    have key : ∀ i j : ℕ, i < j → f i = f j → s ^ (j - i) ∈ U := by
      intro i j hlt hf
      apply hsub
      apply hEu
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' := congrArg (fun φ : E →ₐ[L] Ω => φ ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply] at hy'
      have hj : (s : G L Ω) ^ j = (s : G L Ω) ^ i * (s : G L Ω) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hj] at hy'
      have hy'' : ((s : G L Ω) ^ i) y = ((s : G L Ω) ^ i) (((s : G L Ω) ^ (j - i)) y) := hy'
      have := ((s : G L Ω) ^ i).injective hy''
      show ((s ^ (j - i) : Ine (F := L) A) : G L Ω) • y = y
      rw [Subgroup.coe_pow]
      exact this.symm
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨j - i, Nat.sub_pos_of_lt hlt, key i j hlt hfij⟩
    · exact ⟨i - j, Nat.sub_pos_of_lt hlt, key j i hlt hfij.symm⟩
  have hrs : ∀ s : Ine (F := L) A,
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) = a.ρ (ineIncl h s) := by
    intro s
    obtain ⟨m, hm, hsm⟩ := hpow s
    have hrm : (r (s : G L Ω)) ^ m = 1 := by
      apply Units.ext
      have h1 := hU _ hsm
      rw [hN0, smul_zero, IsNilpotent.exp_zero] at h1
      rw [← map_pow, ← Subgroup.coe_pow, h1, Units.val_one]
    set f : Module.End ℂ (Fin n → ℂ) :=
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) with hf
    have hfm : f ^ m = 1 := by
      rw [hf, ← htoEnd, ← map_pow, ← Units.val_pow_eq_pow_val, hrm, Units.val_one, map_one]
    have hfss : f.IsSemisimple := by
      apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := Polynomial.X ^ m - Polynomial.C 1)
      · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
      · simp [hfm]
    obtain ⟨hcomm, hnil⟩ := hFS (ineIncl h s)
    have hwd : toEndC ι (wdMat t hφ r N (ineIncl h s)) = f := by
      simp only [wdMat, hN0, smul_zero, IsNilpotent.exp_zero, mul_one]
      rfl
    simp only [hwd] at hcomm hnil
    have hss2 : (f - a.ρ (ineIncl h s)).IsSemisimple :=
      hfss.sub_of_commute hcomm.symm (a.semisimple _)
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss2)
  let P : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e : Module.End ℂ (Fin n → ℂ))
  let Pi : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e.symm : Module.End ℂ (Fin n → ℂ))
  have hPPi : P * Pi = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e : Module.End ℂ (Fin n → ℂ)).comp (e.symm : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  have hPiP : Pi * P = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e.symm : Module.End ℂ (Fin n → ℂ)).comp (e : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  let Φ := ι.symm.toRingHom.mapMatrix (m := Fin n)
  let g : GL (Fin n) (Qbar l) :=
    ⟨Φ P, Φ Pi, by rw [← map_mul, hPPi, map_one], by rw [← map_mul, hPiP, map_one]⟩
  refine ⟨g, fun s => ?_⟩
  have hA : a.ρ (ineIncl h s) = (e.symm : Module.End ℂ (Fin n → ℂ)).comp
      ((b.ρ (ineIncl h s)).comp (e : Module.End ℂ (Fin n → ℂ))) := by
    apply LinearMap.ext
    intro v
    simp [← he1]
  have hR : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι =
      Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P := by
    have h1 := congrArg LinearMap.toMatrix' (hrs s)
    rw [LinearMap.toMatrix'_toLin', hA, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hbρ s,
      LinearMap.toMatrix'_toLin', ← mul_assoc] at h1
    rw [h1]
    rfl
  have hback : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Φ ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
    ext i j
    simp [Φ]
  show Φ P * (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * Φ Pi = _
  rw [hback, hR, ← map_mul, ← map_mul]
  rw [show P * (Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P) * Pi =
      Matrix.diagonal (fun i => ι (χ i s : Qbar l)) by
    rw [← mul_assoc, ← mul_assoc, hPPi, one_mul, mul_assoc, hPPi, mul_one]]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Φ]
  · simp [Φ, Matrix.diagonal_apply_ne _ hij]
