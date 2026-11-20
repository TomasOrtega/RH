import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.H1cZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcScalDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Establish `h1` using `hD.xvan D.al (by simp)`. Establish `h2` using `hD.xvan D.be (by simp)`. Establish `h3` using `hD.xvan D.th (by simp)`. Simplify using `only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hj`. Break down `hj with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases.

Establish `e : D.al ^ wAl.1 * D.Psi ^ wAl.2 = D.al` using `by simp [wAl]`. Rewrite using `[e]`. Conclude with `⟨h1.1, by decide, 2, 3, by decide, by simp [Raw.ps]⟩`. Establish `e : D.al ^ (-wAl).1 * D.Psi ^ (-wAl).2 = D.al⁻¹` using `by simp [wAl]`. Rewrite using `[e]`.

Conclude with `⟨h1.2, by decide, 3, 2, by decide, by simp [Raw.ps]⟩`. Establish `e : D.al ^ wBe.1 * D.Psi ^ wBe.2 = D.be` using `by simp [wBe, Raw.be, mul_comm]`. Rewrite using `[e]`. Conclude with `⟨h2.1, by decide, 1, 2, by decide, by simp [Raw.ps, Raw.be]⟩`. Establish `e : D.al ^ (-wBe).1 * D.Psi ^ (-wBe).2 = D.be⁻¹` using `by simp [wBe, Raw.be, mul_comm]`.

Rewrite using `[e]`. Conclude with `⟨h2.2, by decide, 2, 1, by decide, by simp [Raw.ps, Raw.be]⟩`. Establish `e : D.al ^ wTh.1 * D.Psi ^ wTh.2 = D.th` using `by simp [wTh, Raw.th]`. Rewrite using `[e]`. Conclude with `⟨h3.1, by decide, 0, 3, by decide, by simp [Raw.ps]⟩`.

Establish `e : D.al ^ (-wTh).1 * D.Psi ^ (-wTh).2 = D.th⁻¹` using `by simp [wTh, Raw.th, mul_comm]`. Rewrite using `[e]`. Conclude with `⟨h3.2, by decide, 3, 0, by decide, by simp [Raw.ps]⟩`.
-/
private theorem nums_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) {j : ℤ × ℤ} (hj : j ∈ oddRoots) :
    D.XVan (D.al ^ j.1 * D.Psi ^ j.2) ∧ (j.1 = 1 ∨ j.1 = -1) ∧
      ∃ a b, lamW a ≠ lamW b ∧ D.al ^ j.1 * D.Psi ^ j.2 * D.ps b = D.ps a := by
  have h1 := hD.xvan D.al (by simp)
  have h2 := hD.xvan D.be (by simp)
  have h3 := hD.xvan D.th (by simp)
  simp only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : D.al ^ wAl.1 * D.Psi ^ wAl.2 = D.al := by simp [wAl]
    rw [e]
    exact ⟨h1.1, by decide, 2, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wAl).1 * D.Psi ^ (-wAl).2 = D.al⁻¹ := by simp [wAl]
    rw [e]
    exact ⟨h1.2, by decide, 3, 2, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ wBe.1 * D.Psi ^ wBe.2 = D.be := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.1, by decide, 1, 2, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ (-wBe).1 * D.Psi ^ (-wBe).2 = D.be⁻¹ := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.2, by decide, 2, 1, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ wTh.1 * D.Psi ^ wTh.2 = D.th := by simp [wTh, Raw.th]
    rw [e]
    exact ⟨h3.1, by decide, 0, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wTh).1 * D.Psi ^ (-wTh).2 = D.th⁻¹ := by simp [wTh, Raw.th, mul_comm]
    rw [e]
    exact ⟨h3.2, by decide, 3, 0, by decide, by simp [Raw.ps]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h`.
-/
private theorem nums_lc {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

/- English proof (translation)
Establish `hlc : ∀ m, IsLocallyConstant fun g => ρ g m` using `fun m s => (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (by`. Use `((nums_lc γ (Subgroup.isOpen_mono hKγ hK)).comp fun u => (u : k) • m) s` as an intermediate fact. Simplify using `only [Function.comp_def, ← hγ] at this`. Conclude with `this)`. Take `⟨c1, -, c3⟩` from `X.galCount ⟨P.loc.lf, P.loc.lt, P.loc.le, P.gf, P.ge, P.pt⟩ Ω l v0 hG k M ρ hlc (fun q _ g _ hg => LinearMap.ext fun m => by`.

Rewrite using `[hγ, show γ g = 1 from hKγ hg]`. Use the proof step `simp) σ hσ`. Take `⟨s1, s2, s3⟩` from `X.scalDim (ρ.comp (toGS Ω SP)) γ (X.cycK Ω l k) hγ`. Rewrite `c3` using `[s3 hd, add_zero]`. Conclude with `⟨c1, fun e => c3.trans (congrArg _ (s1 σ e)), fun e => c3.trans (congrArg _ (s2 σ e))⟩`.
-/
private theorem nums_gen (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k] [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (hd : Module.finrank k M = 0 ∨ ∃ g, γ g ≠ X.cycK Ω l k g) :
    Module.Finite k ((X.galFrame SP T Q v0 pl K).Ob ρ) ∧
      (γ σ = 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ) + Module.finrank k M) ∧
      (Module.finrank k M = 0 ∨ γ σ ≠ 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ)) := by
  have hlc : ∀ m, IsLocallyConstant fun g => ρ g m := fun m s =>
    (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (by
      have := ((nums_lc γ (Subgroup.isOpen_mono hKγ hK)).comp fun u => (u : k) • m) s
      simp only [Function.comp_def, ← hγ] at this
      exact this)
  obtain ⟨c1, -, c3⟩ := X.galCount ⟨P.loc.lf, P.loc.lt, P.loc.le, P.gf, P.ge, P.pt⟩ Ω l v0 hG k M
    ρ hlc (fun q _ g _ hg => LinearMap.ext fun m => by
      rw [hγ, show γ g = 1 from hKγ hg]; simp) σ hσ
  obtain ⟨s1, s2, s3⟩ := X.scalDim (ρ.comp (toGS Ω SP)) γ (X.cycK Ω l k) hγ
  rw [s3 hd, add_zero] at c3
  exact ⟨c1, fun e => c3.trans (congrArg _ (s1 σ e)), fun e => c3.trans (congrArg _ (s2 σ e))⟩

/- English proof (translation)
Use `haveI : Subsingleton M := Module.finrank_zero_iff.1 h`. Conclude with `Module.finrank_zero_of_subsingleton`.
-/
private theorem nums_zero {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] (F : Frame Γ) (ρ : Representation k Γ M) (h : Module.finrank k M = 0) :
    Module.finrank k (F.H1c ρ) = 0 := by
  haveI : Subsingleton M := Module.finrank_zero_iff.1 h
  exact Module.finrank_zero_of_subsingleton

/- English proof (translation)
Substitute `hF` using the available equality. Establish `h2 : (-1 : kˣ) ≠ 1` using `fun e => by`. Establish `e' : ((2 : ℕ) : k) = 0`. Use `congrArg Units.val e` as an intermediate fact. Simplify using `only [Units.val_neg, Units.val_one] at this`.

Use `push_cast`. Take the linear combination `-this`. Conclude with `hG.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 e'))`. Establish `key` using `nums_gen P v0 hG hK ρ γ hγ hKγ hσ`. Distinguish the cases in `hj : j = 0 ∨ j = wPs ∨ j = -wPs`.

Establish `e : γ σ = 1`. Rewrite using `[hcc]`. Apply the tactic sequence `rcases hj with rfl | rfl | rfl <;> simp [wPs]`. Take `⟨a1, a2, -⟩` from `key (Or.inr ⟨σ, by rw [e, k1]; exact h2.symm⟩)`. Use `⟨a1, ?_, fun n1 n2 n3 => by tauto⟩` and prove the remaining obligations.

Rewrite using `[a2 e, hdim]`. Use `congr 1`. Apply the tactic sequence `rcases hj with rfl | rfl | rfl <;> decide`. Rewrite using `[if_neg fun e => hj (Or.inl e), if_neg fun e => hj (Or.inr e), add_zero]`. Distinguish the cases in `ho : j ∈ oddRoots`.

Take `⟨o1, hne⟩` from `hodd ho`. Establish `o2 : ∀ j ∈ oddRoots, j.1 = 1 ∨ j.1 = -1` using `by decide`. Establish `e : γ σ ≠ 1`. Rewrite using `[hcc]`. Apply the tactic sequence `rcases o2 j ho with o | o <;> rw [o] <;> simpa using h2`.

Take `⟨a1, -, a2⟩` from `key (Or.inr ⟨sg l, e1 ▸ hne l hG.l_mem⟩)`. Use `⟨a1, a2 (Or.inr e), fun _ _ _ => ?_⟩` and prove the remaining obligations. Rewrite using `[X.h1cZero Ω l v0 hG hN _ _ ρ γ hγ hKγ (fun v hv => ⟨sg v, hsg v hv, hne v hv⟩) o1, finrank_bot]`. Establish `e : j ∉ wts`. Simplify using `only [wts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]`.

The claim follows by propositional logic. Rewrite `hdim` using `[dimP, if_neg fun e => hj (Or.inl e), if_neg e]`. Take `⟨a1, -, a2⟩` from `key (Or.inl hdim)`. Conclude with `⟨a1, a2 (Or.inl hdim), fun _ _ _ => nums_zero _ _ hdim⟩`.
-/
private theorem nums_all (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hN : K.Normal) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k]
    [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (k1 : X.cycK Ω l k σ = -1) (j : ℤ × ℤ) (hdim : Module.finrank k M = dimP j) (hcc : γ σ = (-1) ^ j.1)
    (sg : ℕ → G ℚ Ω) (hsg : ∀ v ∈ T, sg v ∈ Dec (F := ℚ) (pl v)) (e1 : X.cycK Ω l k (sg l) = 1)
    (hodd : j ∈ oddRoots → X.Van T pl K γ ∧ ∀ v ∈ T, γ (sg v) ≠ 1)
    (F : Frame (GS Ω SP)) (hF : F = X.galFrame SP T Q v0 pl K) :
    Module.Finite k (F.Ob ρ) ∧
    Module.finrank k (F.Ob ρ) = Module.finrank k (F.H1c ρ) + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank k (F.H1c ρ) = 0) := by
  subst hF
  have h2 : (-1 : kˣ) ≠ 1 := fun e => by
    have e' : ((2 : ℕ) : k) = 0 := by
      have := congrArg Units.val e
      simp only [Units.val_neg, Units.val_one] at this
      push_cast
      linear_combination -this
    exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 e'))
  have key := nums_gen P v0 hG hK ρ γ hγ hKγ hσ
  by_cases hj : j = 0 ∨ j = wPs ∨ j = -wPs
  · have e : γ σ = 1 := by
      rw [hcc]
      rcases hj with rfl | rfl | rfl <;> simp [wPs]
    obtain ⟨a1, a2, -⟩ := key (Or.inr ⟨σ, by rw [e, k1]; exact h2.symm⟩)
    refine ⟨a1, ?_, fun n1 n2 n3 => by tauto⟩
    rw [a2 e, hdim]
    congr 1
    rcases hj with rfl | rfl | rfl <;> decide
  rw [if_neg fun e => hj (Or.inl e), if_neg fun e => hj (Or.inr e), add_zero]
  by_cases ho : j ∈ oddRoots
  · obtain ⟨o1, hne⟩ := hodd ho
    have o2 : ∀ j ∈ oddRoots, j.1 = 1 ∨ j.1 = -1 := by decide
    have e : γ σ ≠ 1 := by
      rw [hcc]
      rcases o2 j ho with o | o <;> rw [o] <;> simpa using h2
    obtain ⟨a1, -, a2⟩ := key (Or.inr ⟨sg l, e1 ▸ hne l hG.l_mem⟩)
    refine ⟨a1, a2 (Or.inr e), fun _ _ _ => ?_⟩
    rw [X.h1cZero Ω l v0 hG hN _ _ ρ γ hγ hKγ (fun v hv => ⟨sg v, hsg v hv, hne v hv⟩) o1, finrank_bot]
  · have e : j ∉ wts := by
      simp only [wts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [dimP, if_neg fun e => hj (Or.inl e), if_neg e] at hdim
    obtain ⟨a1, -, a2⟩ := key (Or.inl hdim)
    exact ⟨a1, a2 (Or.inl hdim), fun _ _ _ => nums_zero _ _ hdim⟩

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D hD P`. Take `⟨-, f2, -, -, -, -, -, ⟨fc, -⟩, -, -, -, fo, -⟩` from `facts D hD`. Take `⟨hN, hI, hK⟩` from `X.spKer D`. Use `haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by`. Take `⟨-, -, -, -, -, h0, -, hval, -⟩` from `dvrFacts l c.O`.

Rewrite `h0` using `[hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]`. Rewrite using `[← map_natCast (residue c.O), residue_eq_zero_iff]`. Conclude with `h0)`. Use `haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1`. Establish `hTS : D.T ⊆ D.S` using `Finset.insert_subset hD.l_mem (by classical`.

Conclude with `Finset.filter_subset _ _)`. Establish `hU : ∀ p, (p ∈ D.T ∨ p ∈ D.S \ D.T) ↔ p ∈ D.S` using `fun p => by`. Rewrite using `[← Finset.mem_union, Finset.union_sdiff_of_subset hTS]`. Establish `hG : X.GalData l D.SP D.T (D.S \ D.T) D.pl D.rbar.ker` using `⟨hD.l_odd, fun p hp => hD.S_prime p ((hU p).1 hp), Finset.disjoint_sdiff, D.residueChar_mem_levelPrimes, fun v => exists_congr fun p => by rw [hU], fun p hp => hD.pl_over p (hD.S_prime p ((hU p).1 hp)), fun q _ hq => hI (hq.trans (Subgroup.relIndex_dvd_index_of_normal _ _))⟩`. Take `⟨k1, k2⟩` from `X.cycKFacts Ω l (ResidueField c.O)`.

Introduce `rb hrb h j`. Set `γ : G ℚ Ω →* (ResidueField c.O)ˣ` to `(Units.map (residue c.O).toMonoidHom).comp (D.al ^ j.1 * D.Psi ^ j.2)`. Establish `hγ : ∀ g m, FormData.adRep h j (toGS Ω D.SP g) m = (γ g : ResidueField c.O) • m` using `X.spAct D rb hrb h j`. Establish `hKγ : D.rbar.ker ≤ γ.ker` using `fun g hg => Units.ext (hK j g hg)`. Establish `hdim` using `X.spDim c.O (ResidueField c.O) j`.

Establish `hcc : γ D.cc = (-1) ^ j.1` using `by show Units.map (residue c.O).toMonoidHom (D.al D.cc ^ j.1 * D.Psi D.cc ^ j.2) = _`. Rewrite using `[fc, hD.Psi_even, one_zpow, mul_one, map_zpow]`. Use `congr 1`. Establish `e1 : X.cycK Ω l (ResidueField c.O) (D.sg l) = 1` using `Units.ext ((k2 c (residue c.O) _).trans ((hD.om_bar _).symm.trans (f2 l D.residueChar_mem_levelPrimes).2.1))`. Establish `hodd : j ∈ oddRoots → X.Van D.T D.pl D.rbar.ker γ ∧ ∀ v ∈ D.T, γ (D.sg v) ≠ 1` using `fun ho => by`.

Take `⟨o1, -, a, b, hab, o3⟩` from `nums_odd D hD ho`. Use `⟨fun z hz hc hu hT => o1 z hz hc (fun A hA g hg hk => hu A hA g hg hk) hT, fun v hv e => ?_⟩` and prove the remaining obligations. Use `(f2 v hv).2.2 a b hab ?_` and prove the remaining obligations. Establish `e' : Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) = 1` using `congrArg Units.val e`. Rewrite using `[← o3]`.

Use `show residue c.O (((D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) : c.O) * (D.ps b (D.sg v) : c.O)) = _`. Rewrite using `[map_mul]`. Conclude with `(congrArg (· * _) e').trans (one_mul _)`. Establish `hF : D.frame = X.galFrame D.SP D.T (D.S \ D.T) ⟨l, D.residueChar_mem_levelPrimes⟩ D.pl D.rbar.ker`. Unfold `Raw.frame X.galFrame`.

Both sides reduce to the same expression. Conclude with `nums_all P ⟨l, D.residueChar_mem_levelPrimes⟩ hG hN fo (FormData.adRep h j) γ hγ hKγ hD.isCC (k1 _ hD.isCC) j hdim hcc D.sg (fun v hv => (f2 v hv).1) e1 hodd D.frame hF`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.nums :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → D.Nums := by
  intro Ω _ _ _ l hl c D hD P
  obtain ⟨-, f2, -, -, -, -, -, ⟨fc, -⟩, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hN, hI, hK⟩ := X.spKer D
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0)
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  have hTS : D.T ⊆ D.S := Finset.insert_subset hD.l_mem (by
    classical
    exact Finset.filter_subset _ _)
  have hU : ∀ p, (p ∈ D.T ∨ p ∈ D.S \ D.T) ↔ p ∈ D.S := fun p => by
    rw [← Finset.mem_union, Finset.union_sdiff_of_subset hTS]
  have hG : X.GalData l D.SP D.T (D.S \ D.T) D.pl D.rbar.ker :=
    ⟨hD.l_odd, fun p hp => hD.S_prime p ((hU p).1 hp), Finset.disjoint_sdiff, D.residueChar_mem_levelPrimes,
      fun v => exists_congr fun p => by rw [hU], fun p hp => hD.pl_over p (hD.S_prime p ((hU p).1 hp)),
      fun q _ hq => hI (hq.trans (Subgroup.relIndex_dvd_index_of_normal _ _))⟩
  obtain ⟨k1, k2⟩ := X.cycKFacts Ω l (ResidueField c.O)
  intro rb hrb h j
  let γ : G ℚ Ω →* (ResidueField c.O)ˣ := (Units.map (residue c.O).toMonoidHom).comp (D.al ^ j.1 * D.Psi ^ j.2)
  have hγ : ∀ g m, FormData.adRep h j (toGS Ω D.SP g) m = (γ g : ResidueField c.O) • m := X.spAct D rb hrb h j
  have hKγ : D.rbar.ker ≤ γ.ker := fun g hg => Units.ext (hK j g hg)
  have hdim := X.spDim c.O (ResidueField c.O) j
  have hcc : γ D.cc = (-1) ^ j.1 := by
    show Units.map (residue c.O).toMonoidHom (D.al D.cc ^ j.1 * D.Psi D.cc ^ j.2) = _
    rw [fc, hD.Psi_even, one_zpow, mul_one, map_zpow]
    congr 1
  have e1 : X.cycK Ω l (ResidueField c.O) (D.sg l) = 1 :=
    Units.ext ((k2 c (residue c.O) _).trans ((hD.om_bar _).symm.trans (f2 l D.residueChar_mem_levelPrimes).2.1))
  have hodd : j ∈ oddRoots → X.Van D.T D.pl D.rbar.ker γ ∧ ∀ v ∈ D.T, γ (D.sg v) ≠ 1 := fun ho => by
    obtain ⟨o1, -, a, b, hab, o3⟩ := nums_odd D hD ho
    refine ⟨fun z hz hc hu hT => o1 z hz hc (fun A hA g hg hk => hu A hA g hg hk) hT, fun v hv e => ?_⟩
    refine (f2 v hv).2.2 a b hab ?_
    have e' : Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) = 1 := congrArg Units.val e
    rw [← o3]
    show residue c.O (((D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) : c.O) * (D.ps b (D.sg v) : c.O)) = _
    rw [map_mul]
    exact (congrArg (· * _) e').trans (one_mul _)
  have hF : D.frame = X.galFrame D.SP D.T (D.S \ D.T) ⟨l, D.residueChar_mem_levelPrimes⟩ D.pl D.rbar.ker := by
    unfold Raw.frame X.galFrame
    rfl
  exact nums_all P ⟨l, D.residueChar_mem_levelPrimes⟩ hG hN fo (FormData.adRep h j) γ hγ hKγ hD.isCC (k1 _ hD.isCC) j hdim hcc D.sg
    (fun v hv => (f2 v hv).1) e1 hodd D.frame hF
