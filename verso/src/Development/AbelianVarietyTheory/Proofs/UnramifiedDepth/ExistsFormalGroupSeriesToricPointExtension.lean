import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSeriesEqOfEvalAtNilpotentPointsEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPoints

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

/- English proof (translation)
Establish `: (MonoidHom.toAdditiveRight χ).toIntLinearMap = (MonoidHom.toAdditiveRight χ').toIntLinearMap` using `β.ext fun j => congrArg Additive.ofMul (Units.ext (h j))`. Use `MonoidHom.ext fun y => ?_` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (LinearMap.congr_fun this y.toAdd)`.
-/
private theorem chi_ext {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (χ χ' : Multiplicative X →* Sˣ)
    (h : ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = χ' (Multiplicative.ofAdd (β j))) : χ = χ' := by
  have : (MonoidHom.toAdditiveRight χ).toIntLinearMap = (MonoidHom.toAdditiveRight χ').toIntLinearMap :=
    β.ext fun j => congrArg Additive.ofMul (Units.ext (h j))
  refine MonoidHom.ext fun y => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun this y.toAdd)

/- English proof (translation)
Use `⟨MonoidHom.toAdditiveRight.symm (β.constr ℤ (fun j => Additive.ofMul (ht j).isUnit_one_add.unit)).toAddMonoidHom, fun j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Additive.toMul (β.constr ℤ (fun j => Additive.ofMul (ht j).isUnit_one_add.unit) (β j)) : Sˣ) : S) = _`. Rewrite using `[Module.Basis.constr_basis]`. Both sides reduce to the same expression.
-/
private theorem chi_ex {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ χ : Multiplicative X →* Sˣ, ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j := by
  refine ⟨MonoidHom.toAdditiveRight.symm (β.constr ℤ
    (fun j => Additive.ofMul (ht j).isUnit_one_add.unit)).toAddMonoidHom, fun j => ?_⟩
  change ((Additive.toMul (β.constr ℤ (fun j => Additive.ofMul (ht j).isUnit_one_add.unit) (β j)) : Sˣ) : S) = _
  rw [Module.Basis.constr_basis]
  rfl

private def pairAlg (R : Type) {S : Type} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) where
  carrier := {p | p.2 - p.1 ∈ J}
  mul_mem' := fun {a b} ha hb => by
    have : (a * b).2 - (a * b).1 = a.2 * (b.2 - b.1) + (a.2 - a.1) * b.1 := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_right _ ha)
  add_mem' := fun {a b} ha hb => by
    have : (a + b).2 - (a + b).1 = (a.2 - a.1) + (b.2 - b.1) := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem ha hb
  algebraMap_mem' := fun c => by
    change _ ∈ J
    simp

/- English proof (translation)
Set `J : Ideal S` to `Ideal.span (Set.range t)`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : IsNilpotent J := by`. Use `(Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range t).toFinset, by simp [J]⟩).2 ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `ht i`. Set `P : Type` to `pairAlg R J`. Set `ρ : P →ₐ[R] S` to `(AlgHom.fst R S S).comp (pairAlg R J).val`. Set `τ : P →ₐ[R] S` to `(AlgHom.snd R S S).comp (pairAlg R J).val`. Set `σ : S →ₐ[R] P` to `((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun y => by`.

Express the relevant statement in the definitionally equal form `_ ∈ J`. Use the proof step `simp)`. Establish `hinj : ∀ p : P, ρ p = 0 → τ p = 0 → p = 0` using `fun p h1 h2 => Subtype.ext (Prod.ext h1 h2)`. Establish `hker : IsNilpotent (RingHom.ker ρ)`. Use `⟨N + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff]`. Introduce `p hp`. Establish `h1 : RingHom.ker ρ ≤ J.comap τ` using `fun q hq => by`. Establish `h2 : τ q - ρ q ∈ J` using `q.2`. Rewrite `hq` using `[RingHom.mem_ker]`.

Rewrite `h2` using `[hq, sub_zero]`. Then use the resulting hypothesis. Establish `h2` using `Ideal.pow_le_self (I := RingHom.ker ρ) (Nat.succ_ne_zero N) hp`. Establish `h3` using `Ideal.le_comap_pow τ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hp)`. Rewrite `h3` using `[pow_succ, hN, zero_mul, Ideal.mem_comap, Ideal.zero_eq_bot, Ideal.mem_bot]`. Conclude with `hinj p h2 h3`.

Establish `hP : ∃ k, Kills I k P`. Take `⟨k, hk⟩` from `h`. Conclude with `⟨k, fun c hc => hinj _ (by rw [AlgHom.commutes, hk c hc]) (by rw [AlgHom.commutes, hk c hc])⟩`. Set `u : Fin r → P` to `fun j => ⟨(0, t j), by`. Express the relevant statement in the definitionally equal form `t j - 0 ∈ J`.

Rewrite using `[sub_zero]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩⟩`. Establish `hnil : ∀ p : P, ρ p = 0 → IsNilpotent p` using `fun p hp => by`. Take `⟨n, hn⟩` from `hker`. Use `Ideal.pow_mem_pow (show p ∈ RingHom.ker ρ from hp) n` as an intermediate fact.

Rewrite `this` using `[hn]`. Conclude with `⟨n, this⟩`. Take `⟨χ₁, hχ₁⟩` from `chi_ex β u (fun j => hnil _ rfl)`. Establish `h1 : (Units.map (ρ : P →* S)).comp χ₁ = 1` using `chi_ext β _ _ fun j => by`. Express the relevant statement in the definitionally equal form `ρ (χ₁ _ : P) = 1`.

Rewrite using `[hχ₁, map_add, map_one]`. Conclude with `add_zero _`. Take `⟨a, ha, hz⟩` from `hx.surj P S ρ σ (AlgHom.ext fun _ => rfl) hker (E.i P hP χ₁) (by rw [← E.i_nat P S ρ hP h, h1, map_one])`. Use `⟨fun i => τ (a i), fun i => (hnil _ (ha i)).map τ, fun χ hχ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hx.nat P S τ a (fun i => hnil _ (ha i)), ← hz, ← E.i_nat P S τ hP h]`.

Use `congr 1`. Use `chi_ext β _ _ fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = τ (χ₁ _ : P)`. Rewrite using `[hχ₁, map_add, map_one, hχ]`. Both sides reduce to the same expression.
-/
private theorem coord_ex {R : Type} [CommRing R] {I : Ideal R} {G B : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [GrpObj B] {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d r : ℕ} {F : Fin d → PS R 2 d} {x : Fam G d}
    (hx : NilChart G F x) (β : Module.Basis (Fin r) ℤ X) (S : Type) [CommRing S] [Algebra R S]
    (h : ∃ k, Kills I k S) (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ b : Fin d → S, (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
  let J : Ideal S := Ideal.span (Set.range t)
  obtain ⟨N, hN⟩ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range t).toFinset, by simp [J]⟩).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  let P : Type := pairAlg R J
  let ρ : P →ₐ[R] S := (AlgHom.fst R S S).comp (pairAlg R J).val
  let τ : P →ₐ[R] S := (AlgHom.snd R S S).comp (pairAlg R J).val
  let σ : S →ₐ[R] P := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun y => by
    change _ ∈ J
    simp)
  have hinj : ∀ p : P, ρ p = 0 → τ p = 0 → p = 0 := fun p h1 h2 => Subtype.ext (Prod.ext h1 h2)
  have hker : IsNilpotent (RingHom.ker ρ) := by
    refine ⟨N + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro p hp
    have h1 : RingHom.ker ρ ≤ J.comap τ := fun q hq => by
      have h2 : τ q - ρ q ∈ J := q.2
      rw [RingHom.mem_ker] at hq
      rwa [hq, sub_zero] at h2
    have h2 := Ideal.pow_le_self (I := RingHom.ker ρ) (Nat.succ_ne_zero N) hp
    have h3 := Ideal.le_comap_pow τ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hp)
    rw [pow_succ, hN, zero_mul, Ideal.mem_comap, Ideal.zero_eq_bot, Ideal.mem_bot] at h3
    exact hinj p h2 h3
  have hP : ∃ k, Kills I k P := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, fun c hc => hinj _ (by rw [AlgHom.commutes, hk c hc]) (by rw [AlgHom.commutes, hk c hc])⟩
  let u : Fin r → P := fun j => ⟨(0, t j), by
    change t j - 0 ∈ J
    rw [sub_zero]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  have hnil : ∀ p : P, ρ p = 0 → IsNilpotent p := fun p hp => by
    obtain ⟨n, hn⟩ := hker
    have := Ideal.pow_mem_pow (show p ∈ RingHom.ker ρ from hp) n
    rw [hn] at this
    exact ⟨n, this⟩
  obtain ⟨χ₁, hχ₁⟩ := chi_ex β u (fun j => hnil _ rfl)
  have h1 : (Units.map (ρ : P →* S)).comp χ₁ = 1 := chi_ext β _ _ fun j => by
    change ρ (χ₁ _ : P) = 1
    rw [hχ₁, map_add, map_one]
    exact add_zero _
  obtain ⟨a, ha, hz⟩ := hx.surj P S ρ σ (AlgHom.ext fun _ => rfl) hker (E.i P hP χ₁)
    (by rw [← E.i_nat P S ρ hP h, h1, map_one])
  refine ⟨fun i => τ (a i), fun i => (hnil _ (ha i)).map τ, fun χ hχ => ?_⟩
  rw [← hx.nat P S τ a (fun i => hnil _ (ha i)), ← hz, ← E.i_nat P S τ hP h]
  congr 1
  refine chi_ext β _ _ fun j => ?_
  change _ = τ (χ₁ _ : P)
  rw [hχ₁, map_add, map_one, hχ]
  rfl

/- English proof (translation)
Introduce `R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx _ r β`. Establish `hc : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), ∃ b : Fin d → S, ∀ h : ∃ k, Kills I k S, (∀ i, IsNilpotent (t i)) → (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ, (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b`. Introduce `S _ _ t`. Distinguish the cases in `h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (t i)`. Take `⟨b, hb⟩` from `coord_ex E hx β S h.1 t h.2`.

Conclude with `⟨b, fun _ _ => hb⟩`. Conclude with `⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩`. Use `choose c hc using hc`. Establish `hJ : ∀ j : Fin d, ∃ f : PS R 1 r, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin 1 → Fin r → S), True → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S (a 0) j = nv (algebraMap R S) f a`. Introduce `j`.

Use `exists_series_of_natural R I hI 1 r (fun _ _ _ => True) (fun _ _ => trivial) (fun S _ _ a => c S (a 0) j) ?_` and prove the remaining obligations. Introduce `S _ _ S' _ _ φ a _ _ _ h ha`. Establish `h' : ∃ k, Kills I k S'`. Take `⟨k, hk⟩` from `h`. Conclude with `⟨k, fun c hc => by rw [← φ.commutes, hk c hc, map_zero]⟩`.

Take `⟨χ, hχ⟩` from `chi_ex β (a 0) (ha 0)`. Take `⟨h1, h2⟩` from `hc S (a 0) h (ha 0)`. Take `⟨h3, h4⟩` from `hc S' (fun j => φ (a 0 j)) h' (fun i => (ha 0 i).map φ)`. Establish `h5` using `h4 ((Units.map (φ : S →* S')).comp χ) fun j => by`. Express the relevant statement in the definitionally equal form `φ (χ _ : S) = _`.

Rewrite using `[hχ, map_add, map_one]`. Rewrite `h5` using `[E.i_nat S S' φ h h', h2 χ hχ, hx.nat S S' φ _ h1]`. Conclude with `congrFun (hx.inj S' _ _ (fun i => (h1 i).map φ) h3 h5) j`. Use `choose J hJ using hJ`. Establish `hJ' : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), (∃ k, Kills I k S) → (∀ i, IsNilpotent (t i)) → (fun j => nv (algebraMap R S) (J j) ![t]) = c S t`.

Introduce `S _ _ t h ht`. Use function extensionality and compare the values at `j`. Conclude with `(hJ j S ![t] trivial h (fun i => by fin_cases i; exact ht)).symm`. Establish `h0 : ∀ j, MvPowerSeries.constantCoeff (J j) = 0`. Introduce `j`.

Establish `: (MvPowerSeries.C (MvPowerSeries.constantCoeff (J j)) : PS R 1 r) = 0`. Use `eq_of_nv_eq R I inferInstance 1 r _ _ fun S _ _ k hk _ a ha => ?_` and prove the remaining obligations. Take `⟨ψ, h1, h2, -⟩` from `(nv_calculus R S (algebraMap R S) 1 r a ha).1`. Rewrite using `[← h1, ← h1, h2, map_zero]`. Establish `hz : ∀ i : Fin r, IsNilpotent ((0 : Fin r → S) i)` using `fun _ => IsNilpotent.zero`.

Take `⟨h3, h4⟩` from `hc S 0 ⟨k, hk⟩ hz`. Establish `h5` using `h4 1 (fun j => by simp)`. Rewrite `h5` using `[map_one, ← hx.zero S]`. Establish `h6` using `congrFun ((hJ' S 0 ⟨k, hk⟩ hz).trans (hx.inj S _ _ (fun _ => IsNilpotent.zero) h3 h5).symm) j`. Rewrite `h6` using `[(nv_calculus R S (algebraMap R S) 1 r ![0] (fun i => by fin_cases i; exact hz)).2.2.2.2.2 (fun i _ i' _ => by fin_cases i; simp)]`.

Simplify using `using h6`. Simplify using `using congrArg MvPowerSeries.constantCoeff this`. Use `⟨J, ⟨h0, fun j => ?_⟩, fun S _ _ h χ t ht hχ => ?_⟩` and prove the remaining obligations. Use `eq_of_nv_eq R I inferInstance 2 r _ _ fun S _ _ k hk _ a ha => ?_` and prove the remaining obligations. Establish `h : ∃ k, Kills I k S` using `⟨k, hk⟩`.

Take `⟨⟨ψ, hψ, -, hX⟩, -, hs, -⟩` from `nv_calculus R S (algebraMap R S) 2 r a ha`. Establish `hev : ∀ (p : Fin r → PS R 2 r) (t : Fin r → S), (∀ i, MvPowerSeries.constantCoeff (p i) = 0) → (∀ i, ψ (p i) = t i) → (∀ i, IsNilpotent (t i)) → ∀ i, nv (algebraMap R S) (ev (n` using `2) ![p] (J i)) a = c S t i := by`. Introduce `p t hp hpt ht i`. Rewrite using `[← hJ' S t h ht]`. Use `(hs 1 r ![p] (J i) (fun i => by fin_cases i; exact hp)).trans ?_` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `i j`. Use `fin_cases i`. Conclude with `(hψ _).symm.trans (hpt j)`. Establish `hcc : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (ev (n` using `2) ![pt R r l] (J i)) = 0 := by`.

Introduce `l i`. Establish `hp : ∀ q : Fin 1 × Fin r, MvPowerSeries.constantCoeff ((![pt R r l] : Fin 1 → Pt R 2 r) q.1 q.2) = 0`. Introduce and unpack `⟨q, q'⟩`. Use `fin_cases q`. Simplify using `[pt]`.

Conclude with `MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hp) hp (h0 i)`. Establish `hn : ∀ i, IsNilpotent (a 0 i + a 1 i + a 0 i * a 1 i)` using `fun i => (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add (ha 0 i) (ha 1 i)) ((Commute.all _ _).isNilpotent_mul_left (ha 1 i))`. Apply the tactic sequence `rw [hev (gmF R r) _ (fun i => by simp [gmF]) (fun i => by simp [gmF, hX]) hn, hs _ _ _ _ (fun l => by fin_cases l <;> exact hcc _)]`. Take `⟨χ₀, hχ₀⟩` from `chi_ex β (a 0) (ha 0)`. Take `⟨χ₁, hχ₁⟩` from `chi_ex β (a 1) (ha 1)`.

Take `⟨n0, e0⟩` from `hc S (a 0) h (ha 0)`. Take `⟨n1, e1⟩` from `hc S (a 1) h (ha 1)`. Take `⟨n2, e2⟩` from `hc S _ h hn`. Establish `e3` using `e2 (χ₀ * χ₁) fun j => by`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, hχ₀, hχ₁]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `e3` using `[map_mul, e0 _ hχ₀, e1 _ hχ₁, hx.law S _ _ n0 n1]`. Establish `n3 : ∀ k, IsNilpotent (nv (algebraMap R S) (F.F k) ![c S (a 0), c S (a 1)])` using `fun k => ((nv_calculus R S (algebraMap R S) 2 d _ (fun l => by fin_cases l`. Conclude with `n0`. Conclude with `n1)).2.1 _ (F.const k)).1`.

Rewrite using `[← congrFun (hx.inj S _ _ n3 n2 e3) j]`. Use `congr 1`. Use function extensionality and compare the values at `l i`. Use `fin_cases l`. Conclude with `(hev (pt R r 0) (a 0) (fun i => by simp [pt]) (fun i => hX (0, i)) (ha 0) i).symm`.

Conclude with `(hev (pt R r 1) (a 1) (fun i => by simp [pt]) (fun i => hX (1, i)) (ha 1) i).symm`. Rewrite using `[hJ' S t h ht]`. Conclude with `(hc S t h ht).2 χ hχ`.
-/
theorem exists_series_torus : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X), ∃ J : Fin d → PS R 1 r, IsHomF (gmF R r) F.F J ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx _ r β
  classical
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), ∃ b : Fin d → S,
      ∀ h : ∃ k, Kills I k S, (∀ i, IsNilpotent (t i)) → (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
    intro S _ _ t
    by_cases h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (t i)
    · obtain ⟨b, hb⟩ := coord_ex E hx β S h.1 t h.2
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose c hc using hc
  have hJ : ∀ j : Fin d, ∃ f : PS R 1 r, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin 1 → Fin r → S),
      True → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S (a 0) j = nv (algebraMap R S) f a := by
    intro j
    refine exists_series_of_natural R I hI 1 r (fun _ _ _ => True) (fun _ _ => trivial) (fun S _ _ a => c S (a 0) j) ?_
    intro S _ _ S' _ _ φ a _ _ _ h ha
    have h' : ∃ k, Kills I k S' := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, fun c hc => by rw [← φ.commutes, hk c hc, map_zero]⟩
    obtain ⟨χ, hχ⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨h1, h2⟩ := hc S (a 0) h (ha 0)
    obtain ⟨h3, h4⟩ := hc S' (fun j => φ (a 0 j)) h' (fun i => (ha 0 i).map φ)
    have h5 := h4 ((Units.map (φ : S →* S')).comp χ) fun j => by
      change φ (χ _ : S) = _
      rw [hχ, map_add, map_one]
    rw [E.i_nat S S' φ h h', h2 χ hχ, hx.nat S S' φ _ h1] at h5
    exact congrFun (hx.inj S' _ _ (fun i => (h1 i).map φ) h3 h5) j
  choose J hJ using hJ
  have hJ' : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), (∃ k, Kills I k S) →
      (∀ i, IsNilpotent (t i)) → (fun j => nv (algebraMap R S) (J j) ![t]) = c S t := by
    intro S _ _ t h ht
    funext j
    exact (hJ j S ![t] trivial h (fun i => by fin_cases i; exact ht)).symm
  have h0 : ∀ j, MvPowerSeries.constantCoeff (J j) = 0 := by
    intro j
    have : (MvPowerSeries.C (MvPowerSeries.constantCoeff (J j)) : PS R 1 r) = 0 := by
      refine eq_of_nv_eq R I inferInstance 1 r _ _ fun S _ _ k hk _ a ha => ?_
      obtain ⟨ψ, h1, h2, -⟩ := (nv_calculus R S (algebraMap R S) 1 r a ha).1
      rw [← h1, ← h1, h2, map_zero]
      have hz : ∀ i : Fin r, IsNilpotent ((0 : Fin r → S) i) := fun _ => IsNilpotent.zero
      obtain ⟨h3, h4⟩ := hc S 0 ⟨k, hk⟩ hz
      have h5 := h4 1 (fun j => by simp)
      rw [map_one, ← hx.zero S] at h5
      have h6 := congrFun ((hJ' S 0 ⟨k, hk⟩ hz).trans
        (hx.inj S _ _ (fun _ => IsNilpotent.zero) h3 h5).symm) j
      rw [(nv_calculus R S (algebraMap R S) 1 r ![0] (fun i => by fin_cases i; exact hz)).2.2.2.2.2
        (fun i _ i' _ => by fin_cases i; simp)] at h6
      simpa using h6
    simpa using congrArg MvPowerSeries.constantCoeff this
  refine ⟨J, ⟨h0, fun j => ?_⟩, fun S _ _ h χ t ht hχ => ?_⟩
  · refine eq_of_nv_eq R I inferInstance 2 r _ _ fun S _ _ k hk _ a ha => ?_
    have h : ∃ k, Kills I k S := ⟨k, hk⟩
    obtain ⟨⟨ψ, hψ, -, hX⟩, -, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 r a ha
    have hev : ∀ (p : Fin r → PS R 2 r) (t : Fin r → S), (∀ i, MvPowerSeries.constantCoeff (p i) = 0) →
        (∀ i, ψ (p i) = t i) → (∀ i, IsNilpotent (t i)) →
        ∀ i, nv (algebraMap R S) (ev (n := 2) ![p] (J i)) a = c S t i := by
      intro p t hp hpt ht i
      rw [← hJ' S t h ht]
      refine (hs 1 r ![p] (J i) (fun i => by fin_cases i; exact hp)).trans ?_
      congr 1
      funext i j
      fin_cases i
      exact (hψ _).symm.trans (hpt j)
    have hcc : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (ev (n := 2) ![pt R r l] (J i)) = 0 := by
      intro l i
      have hp : ∀ q : Fin 1 × Fin r, MvPowerSeries.constantCoeff ((![pt R r l] : Fin 1 → Pt R 2 r) q.1 q.2) = 0 := by
        rintro ⟨q, q'⟩
        fin_cases q
        simp [pt]
      exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hp) hp (h0 i)
    have hn : ∀ i, IsNilpotent (a 0 i + a 1 i + a 0 i * a 1 i) := fun i =>
      (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add (ha 0 i) (ha 1 i))
        ((Commute.all _ _).isNilpotent_mul_left (ha 1 i))
    rw [hev (gmF R r) _ (fun i => by simp [gmF]) (fun i => by simp [gmF, hX]) hn,
      hs _ _ _ _ (fun l => by fin_cases l <;> exact hcc _)]
    obtain ⟨χ₀, hχ₀⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨χ₁, hχ₁⟩ := chi_ex β (a 1) (ha 1)
    obtain ⟨n0, e0⟩ := hc S (a 0) h (ha 0)
    obtain ⟨n1, e1⟩ := hc S (a 1) h (ha 1)
    obtain ⟨n2, e2⟩ := hc S _ h hn
    have e3 := e2 (χ₀ * χ₁) fun j => by
      rw [MonoidHom.mul_apply, Units.val_mul, hχ₀, hχ₁]
      ring
    rw [map_mul, e0 _ hχ₀, e1 _ hχ₁, hx.law S _ _ n0 n1] at e3
    have n3 : ∀ k, IsNilpotent (nv (algebraMap R S) (F.F k) ![c S (a 0), c S (a 1)]) := fun k =>
      ((nv_calculus R S (algebraMap R S) 2 d _ (fun l => by
        fin_cases l
        · exact n0
        · exact n1)).2.1 _ (F.const k)).1
    rw [← congrFun (hx.inj S _ _ n3 n2 e3) j]
    congr 1
    funext l i
    fin_cases l
    · exact (hev (pt R r 0) (a 0) (fun i => by simp [pt]) (fun i => hX (0, i)) (ha 0) i).symm
    · exact (hev (pt R r 1) (a 1) (fun i => by simp [pt]) (fun i => hX (1, i)) (ha 1) i).symm
  · rw [hJ' S t h ht]
    exact (hc S t h ht).2 χ hχ

end GlobalTheory.ChF
