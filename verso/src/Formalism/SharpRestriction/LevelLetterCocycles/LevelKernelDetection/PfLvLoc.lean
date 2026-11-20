import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

namespace LvLoc

open Classical in

def evKD (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

/- English proof (translation)
Use `show TensorProduct.piScalarRight LL LL D _ (TensorProduct.comm LL (KsW W s) D (TensorProduct.comm LL D (KsW W s) ((TensorProduct.piScalarRight LL LL D _).symm F))) = F`. Rewrite using `[← TensorProduct.comm_symm LL (KsW W s) D, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem evKD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (F : Rs LL PD.p s → D) :
    evKD W s D (toKsD W s D F) = F := by
  classical
  show TensorProduct.piScalarRight LL LL D _ (TensorProduct.comm LL (KsW W s) D
    (TensorProduct.comm LL D (KsW W s) ((TensorProduct.piScalarRight LL LL D _).symm F))) = F
  rw [← TensorProduct.comm_symm LL (KsW W s) D, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul f d`. Simplify using `[evKD, tD, LinearMap.rTensor_tmul, TensorProduct.piScalarRightHom_tmul, precomp_apply]`. Consider the case `add z z' hz hz' => rw [map_add, map_add, Pi.add_apply, hz, hz', map_add, Pi.add_apply]`.
-/
theorem evKD_tD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (z : KsW W s ⊗[LL] D) (ξ : Rs LL PD.p s) :
    evKD W s D (tD D (precomp LL PD.p s b) z) ξ = evKD W s D z (powR LL PD.p s b ξ) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f d =>
    simp [evKD, tD, LinearMap.rTensor_tmul, TensorProduct.piScalarRightHom_tmul, precomp_apply]
  | add z z' hz hz' => rw [map_add, map_add, Pi.add_apply, hz, hz', map_add, Pi.add_apply]

/- English proof (translation)
Apply `(evKD W s D).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `ξ`. Rewrite using `[evKD_tD, evKD_toKsD, evKD_toKsD]`.
-/
theorem tD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (F : Rs LL PD.p s → D) :
    tD D (precomp LL PD.p s b) (toKsD W s D F) = toKsD W s D (fun ξ => F (powR LL PD.p s b ξ)) := by
  apply (evKD W s D).injective
  funext ξ
  rw [evKD_tD, evKD_toKsD, evKD_toKsD]

/- English proof (translation)
Establish `: NeZero (PD.p ^ (s + 1))` using `⟨(pos_pow PD.p s).ne'⟩`. Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]`. Both sides reduce to the same expression.
-/
theorem dvd_sub_val (s : ℕ) (ω : ℤ_[PD.p]ˣ) :
    (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ (ω : ℤ_[PD.p]) - ((redU PD.p s ω : ZMod (PD.p ^ (s + 1))).val : ℤ_[PD.p]) := by
  have : NeZero (PD.p ^ (s + 1)) := ⟨(pos_pow PD.p s).ne'⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_eq_zero]
  rfl

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

/- English proof (translation)
Introduce `j`. Take `⟨g, hgD, hgχ⟩` from `hω j`. Apply `HahnModule.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Use `show ((((levW W uZ ιZ s).a j) ^ k : LLˣ) : LL) • tD (Dc W T c) (precomp LL PD.p s (redU PD.p s j.1)) (coefN Lb s T c y k) = coefN Lb s T c y k`.

Simplify using `only [coefN]`. Rewrite using `[tD_toKsD, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `ζ`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hx : W.γD T g (y : W.DD T) ∈ W.N T` using `by rw [hy g hgD]; exact y.2`. Establish `hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1))` using `(mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2`. Establish `hval : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (((redU PD.p s j.1 : ZMod (PD.p ^ (s + 1))).val : ℕ) : LL))`. Rewrite using `[hgχ, ← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub]`. Conclude with `hv s _ (dvd_sub_val s j.1)`.

Establish `key` using `levB_Γ T hT g c ζ _ (s + 1) _ hprim hval rfl y hx k`. Establish `hyy : (⟨W.γD T g (y : W.DD T), hx⟩ : ↥(W.N T)) = y` using `Subtype.ext (hy g hgD)`. Rewrite `key` using `[hyy, hgχ]`. Rewrite using `[Pi.smul_apply, SetLike.val_smul]`. Use `show _ • Lb.levB T c (powR LL PD.p s (redU PD.p s j.1) ζ : LL) y k = Lb.levB T c ζ y k`.

Rewrite using `[key, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
theorem expN_inv (Lb : LevB W) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)))
    (s : ℕ) (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) :
    (levW W uZ ιZ s).Inv (D := Dc W T c) (expN Lb s T c y) := by
  intro j
  obtain ⟨g, hgD, hgχ⟩ := hω j
  apply HahnModule.ext
  funext k
  show ((((levW W uZ ιZ s).a j) ^ k : LLˣ) : LL) •
      tD (Dc W T c) (precomp LL PD.p s (redU PD.p s j.1)) (coefN Lb s T c y k) = coefN Lb s T c y k
  simp only [coefN]
  rw [tD_toKsD, ← map_smul]
  congr 1
  funext ζ
  apply Subtype.ext
  have hx : W.γD T g (y : W.DD T) ∈ W.N T := by rw [hy g hgD]; exact y.2
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hval : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) -
      (((redU PD.p s j.1 : ZMod (PD.p ^ (s + 1))).val : ℕ) : LL)) := by
    rw [hgχ, ← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub]
    exact hv s _ (dvd_sub_val s j.1)
  have key := levB_Γ T hT g c ζ _ (s + 1) _ hprim hval rfl y hx k
  have hyy : (⟨W.γD T g (y : W.DD T), hx⟩ : ↥(W.N T)) = y := Subtype.ext (hy g hgD)
  rw [hyy, hgχ] at key
  rw [Pi.smul_apply, SetLike.val_smul]
  show _ • Lb.levB T c (powR LL PD.p s (redU PD.p s j.1) ζ : LL) y k = Lb.levB T c ζ y k
  rw [key, Units.val_zpow_eq_zpow_val]
  rfl

end LvLoc

open LvLoc

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

/- English proof (translation)
Introduce `s x hx j`. Establish `he` using `expN_inv (c := c) (uZ := uZ) Lb hT levB_Γ hω hv s ⟨C.t c x, hx⟩ fun δ hδ => C.t_Δ c x δ hδ`. Establish `hz` using `hΔ s j κ`. Use `show Level.δ (levW W uZ ιZ s) j (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩) = Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩`. Distinguish the cases in `hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))`.

Take `⟨u, hu⟩` from `hu`. Rewrite `hz`, the goal using `[← hu]`. Rewrite using `[Ring.inverse_unit]`. Establish `h1 : (u : HahnSeries ℤ (KsW W s)) • Level.δ (levW W uZ ιZ s) j (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) = expN Lb s T c ⟨C.t c x, hx⟩` using `by conv_lhs => rw [← hz]`. Rewrite using `[Level.δ, ← graded_semilinear_holds, smul_smul, Units.mul_inv, one_smul]`.

Conclude with `he j`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Use `_ = _ := by rw [h1]`. Rewrite using `[Ring.inverse_non_unit _ hu, zero_smul]`.

Conclude with `map_zero _`.
-/
theorem locInv_holds (Lb : LevB W) (C : Coord W (baseIdOf hR) T) (κ : PowerSeries O)
    (hΔ : DeltaRho hR uZ ιZ c) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z))) :
    LocInv Lb C c uZ ιZ κ := by
  intro s x hx j
  have he := expN_inv (c := c) (uZ := uZ) Lb hT levB_Γ hω hv s ⟨C.t c x, hx⟩ fun δ hδ => C.t_Δ c x δ hδ
  have hz := hΔ s j κ
  show Level.δ (levW W uZ ιZ s) j
      (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩) =
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩
  by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at hz ⊢
    rw [Ring.inverse_unit]
    have h1 : (u : HahnSeries ℤ (KsW W s)) • Level.δ (levW W uZ ιZ s) j
        (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        expN Lb s T c ⟨C.t c x, hx⟩ := by
      conv_lhs => rw [← hz]
      rw [Level.δ, ← graded_semilinear_holds, smul_smul, Units.mul_inv, one_smul]
      exact he j
    calc Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        ((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • ((u : HahnSeries ℤ (KsW W s)) •
          Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [h1]
  · rw [Ring.inverse_non_unit _ hu, zero_smul]
    exact map_zero _

namespace LvLoc

/- English proof (translation)
The claim follows from `| 0 => fun v hv => by simpa [Formalism.ExponentWindows.E.Lat.phiIt] using hv | k + 1 => fun v hv => by have ih := phiIt_mem L m hP i k v hv have e1 : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring have h := hP (i + ((k + 1 : ℕ) : ZMod n)) _ (by rw [e1]; e …`.
-/
theorem phiIt_mem {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Formalism.ExponentWindows.E.Lat Bs n V) (m : ℕ) (hP : ∀ i, L.P5M i m) (i : ZMod n) :
    ∀ (k : ℕ), ∀ v ∈ L.N i, (∏ s ∈ Finset.range k, Bs.p s ^ m) • L.phiIt i k v ∈ L.N (i + (k : ZMod n))
  | 0 => fun v hv => by simpa [Formalism.ExponentWindows.E.Lat.phiIt] using hv
  | k + 1 => fun v hv => by
    have ih := phiIt_mem L m hP i k v hv
    have e1 : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    have h := hP (i + ((k + 1 : ℕ) : ZMod n)) _ (by rw [e1]; exact ih)
    rw [L.φ_semi, smul_smul] at h
    have e : (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) =
        Bs.q ^ m * Bs.φ (∏ s ∈ Finset.range k, Bs.p s ^ m) := by
      rw [Finset.prod_range_succ', map_prod, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [map_pow, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']
    show (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) • L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v) ∈
      L.N (i + ((k + 1 : ℕ) : ZMod n))
    rw [e]
    exact h

/- English proof (translation)
Introduce `x hx`. Use `show C.t i ((baseIdOf hR).Bs.q ^ m • (latOf C).φ i x) ∈ W.N T`. Rewrite using `[C.t_smul, map_pow, BaseId.d_q]`. Establish `h1 : C.t i ((latOf C).φ i x) = W.φD T (C.t (i - 1) x)` using `by show (((C.θ i) ((C.θ i).symm (φl W T i (C.θ (i - 1) x))) : ↥(DDl W T i)) : W.DD T) = _`. Rewrite using `[AddEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Establish `h2 : C.t (i - 1) x ∈ W.Nl T (i - 1)` using `Submodule.mem_map.2 ⟨_, hx, C.t_letter (i - 1) x⟩`. Establish `h4` using `qP_pow_mem hs hRA (W.N T) (hp5.1 i _ h2)`. Establish `e : qP W ^ m = qP W ^ (m - M i) * qP W ^ M i` using `by rw [← pow_add, Nat.sub_add_cancel (hm i)]`.

Rewrite using `[e, mul_smul]`. Conclude with `(W.N T).smul_mem _ h4`.
-/
theorem latOf_P5M_of_p5_of_le (C : Coord W (baseIdOf hR) T) {M h : ZMod n → ℕ} (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m) (i : ZMod n) : (latOf C).P5M i m := by
  intro x hx
  show C.t i ((baseIdOf hR).Bs.q ^ m • (latOf C).φ i x) ∈ W.N T
  rw [C.t_smul, map_pow, BaseId.d_q]
  have h1 : C.t i ((latOf C).φ i x) = W.φD T (C.t (i - 1) x) := by
    show (((C.θ i) ((C.θ i).symm (φl W T i (C.θ (i - 1) x))) : ↥(DDl W T i)) : W.DD T) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [h1]
  have h2 : C.t (i - 1) x ∈ W.Nl T (i - 1) := Submodule.mem_map.2 ⟨_, hx, C.t_letter (i - 1) x⟩
  have h4 := qP_pow_mem hs hRA (W.N T) (hp5.1 i _ h2)
  have e : qP W ^ m = qP W ^ (m - M i) * qP W ^ M i := by rw [← pow_add, Nat.sub_add_cancel (hm i)]
  rw [e, mul_smul]
  exact (W.N T).smul_mem _ h4

end LvLoc

/- English proof (translation)
Introduce `w hw`. Establish `hL : ∀ i, (latOf C).P5M i m` using `latOf_P5M_of_p5_of_le C (hP5 T M h hT hJ) hs hRA m hm`. Rewrite using `[hκ, mul_comm, mul_smul]`. Establish `hw' : Λ • w ∈ (latOf C).pull (c - (ell : ZMod n)) ell` using `hw`. Establish `hc : c - (ell : ZMod n) + (ell : ZMod n) = c` using `sub_add_cancel _ _`.

Use `Submodule.span_induction (p := fun y _ => (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) • y ∈ (latOf C).N c) ?_ ?_ ?_ ?_ hw'` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Use `phiIt_mem (latOf C) m hL (c - (ell : ZMod n)) ell u hu` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `y z _ _ hy hz`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hy hz`. Introduce `a y _ hy`.

Rewrite using `[smul_smul, mul_comm, ← smul_smul]`. Conclude with `Submodule.smul_mem _ a hy`.
-/
theorem kap_holds (C : Coord W (baseIdOf hR) T) (ell : ℕ) (Λ κ : PowerSeries O) {M h : ZMod n → ℕ}
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) (hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m)
    (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    ∀ w ∈ (latOf C).W c ell Λ, κ • w ∈ (latOf C).N c := by
  intro w hw
  have hL : ∀ i, (latOf C).P5M i m := latOf_P5M_of_p5_of_le C (hP5 T M h hT hJ) hs hRA m hm
  rw [hκ, mul_comm, mul_smul]
  have hw' : Λ • w ∈ (latOf C).pull (c - (ell : ZMod n)) ell := hw
  have hc : c - (ell : ZMod n) + (ell : ZMod n) = c := sub_add_cancel _ _
  refine Submodule.span_induction (p := fun y _ =>
    (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) • y ∈ (latOf C).N c) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨u, hu, rfl⟩
    have := phiIt_mem (latOf C) m hL (c - (ell : ZMod n)) ell u hu
    rwa [hc] at this
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz
  · intro a y _ hy
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hy

end Formalism.MainNotions.N.Ln03.Pf
