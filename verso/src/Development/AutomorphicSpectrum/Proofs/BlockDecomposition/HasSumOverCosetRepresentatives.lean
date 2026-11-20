import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.OrbitSums

/- English proof (translation)
Use `Fintype.ofFinite K` as an intermediate fact. Establish `hn' : Summable (fun _ : K => ‖(1 : ℂ)‖)` using `(hasSum_fintype _).summable`. Simplify using `using summable_mul_of_summable_norm (f := G) (g := fun _ : K => (1:ℂ)) hn hn'`.
-/
theorem summable_fst_of_norm {Q K : Type} [Finite K] (G : Q → ℂ)
    (hn : Summable (fun q => ‖G q‖)) : Summable (fun p : Q × K => G p.1) := by
  have := Fintype.ofFinite K
  have hn' : Summable (fun _ : K => ‖(1 : ℂ)‖) := (hasSum_fintype _).summable
  simpa using summable_mul_of_summable_norm (f := G) (g := fun _ : K => (1:ℂ)) hn hn'

/- English proof (translation)
Use `Fintype.ofFinite K` as an intermediate fact. Establish `hs : Summable (fun p : Q × K => G p.1)` using `summable_fst_of_norm G h2.summable.norm`. Establish `hf : ∀ q, HasSum (fun k : K => G (q, k).1) ((Nat.card K : ℂ) * G q)` using `fun q => by`. Use `hasSum_fintype (fun _ : K => G q)` as an intermediate fact. Simplify `this` using `[Nat.card_eq_fintype_card]`.

Establish `h5` using `hs.hasSum.prod_fiberwise hf`. Establish `h6 : HasSum (fun q => (Nat.card K : ℂ) * G q) ((Nat.card K : ℂ) * s)` using `h2.mul_left _`. Rewrite using `[h6.unique h5]`. Conclude with `hs.hasSum`.
-/
theorem hasSum_fst_prod {Q K : Type} [Finite K] (G : Q → ℂ) (s : ℂ) (h2 : HasSum G s) :
    HasSum (fun p : Q × K => G p.1) ((Nat.card K : ℂ) * s) := by
  have := Fintype.ofFinite K
  have hs : Summable (fun p : Q × K => G p.1) := summable_fst_of_norm G h2.summable.norm
  have hf : ∀ q, HasSum (fun k : K => G (q, k).1) ((Nat.card K : ℂ) * G q) := fun q => by
    have := hasSum_fintype (fun _ : K => G q)
    simpa [Nat.card_eq_fintype_card] using this
  have h5 := hs.hasSum.prod_fiberwise hf
  have h6 : HasSum (fun q => (Nat.card K : ℂ) * G q) ((Nat.card K : ℂ) * s) := h2.mul_left _
  rw [h6.unique h5]
  exact hs.hasSum

/- English proof (translation)
Establish `h5` using `((Subgroup.groupEquivQuotientProdSubgroup (s := K)).hasSum_iff (f := fun p : (H ⧸ K) × K => G p.1)).2 (hasSum_fst_prod G s h2)`. Establish `hfst : ∀ h : H, ((Subgroup.groupEquivQuotientProdSubgroup (s` using `K)) h).1 = QuotientGroup.mk h := fun h => rfl`. Simplify `h5` using `only [Function.comp_def, hfst]`.
-/
theorem hasSum_comp_mk {H : Type} [CommGroup H] (K : Subgroup H) [Finite K] (G : H ⧸ K → ℂ)
    (s : ℂ) (h2 : HasSum G s) :
    HasSum (fun h : H => G (QuotientGroup.mk h)) ((Nat.card K : ℂ) * s) := by
  have h5 := ((Subgroup.groupEquivQuotientProdSubgroup (s := K)).hasSum_iff
      (f := fun p : (H ⧸ K) × K => G p.1)).2 (hasSum_fst_prod G s h2)
  have hfst : ∀ h : H, ((Subgroup.groupEquivQuotientProdSubgroup (s := K)) h).1
      = QuotientGroup.mk h := fun h => rfl
  simpa only [Function.comp_def, hfst] using h5

/- English proof (translation)
Set `φ' : H →* Multiplicative A` to `MonoidHom.mk' (fun h => Multiplicative.ofAdd (φ h)) (fun a b => by simp [hφ])`. Set `K : Subgroup H` to `φ'.ker`. Establish `memK : ∀ h, h ∈ K ↔ φ h = 0` using `fun h => by`. Simplify using `[K, φ', MonoidHom.mem_ker]`. Set `bar : (H ⧸ K) → A` to `fun q => Multiplicative.toAdd (QuotientGroup.kerLift φ' q)`.

Establish `bar_inj : Function.Injective bar` using `fun a b hab => QuotientGroup.kerLift_injective φ' (Multiplicative.toAdd.injective hab)`. Establish `barT : ∀ q, bar q ∈ T` using `fun q => by`. Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `hT h`. Set `ψ : (H ⧸ K) × R → T` to `fun p => ⟨(p.2 : A) + bar p.1, T.add_mem (hR _ p.2.2) (barT _)⟩`.

Establish `ψbij : Function.Bijective ψ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, r, hr⟩ ⟨q', r', hr'⟩ h`. Establish `h' : r + bar q = r' + bar q'` using `congrArg Subtype.val h`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`.

Take `⟨g', rfl⟩` from `QuotientGroup.mk_surjective q'`. Establish `hm : r + φ g ∈ T` using `T.add_mem (hR _ hr) (hT g)`. Establish `hrr : r = r'` using `(hu _ hm).unique ⟨hr, g, rfl⟩ ⟨hr', g', h'⟩`. Substitute `hrr` using the available equality. Establish `: bar (QuotientGroup.mk g) = bar (QuotientGroup.mk g')` using `add_left_cancel h'`.

Rewrite using `[bar_inj this]`. Introduce and unpack `⟨m, hm⟩`. Take `⟨r, ⟨hr, h, rfl⟩, -⟩` from `hu m hm`. Conclude with `⟨(QuotientGroup.mk h, ⟨r, hr⟩), rfl⟩`. Establish `h1 : HasSum (fun p : (H ⧸ K) × R => F ((p.2 : A) + bar p.1)) s` using `((Equiv.ofBijective ψ ψbij).hasSum_iff (f := fun m : T => F m)).2 hs`.

Establish `h2 : HasSum (fun q : H ⧸ K => ∑ r ∈ R, F (r + bar q)) s`. Use `h1.prod_fiberwise (fun q => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort R (fun r => F (r + bar q))]`. Conclude with `hasSum_fintype (fun r : R => F ((r : A) + bar q))`. Establish `hKf : Finite K` using `Finite.of_equiv _ (Equiv.subtypeEquivRight (fun h => (memK h).symm))`.

Establish `h5` using `hasSum_comp_mk K _ s h2`. Establish `hc : Nat.card K = Nat.card {h : H // φ h = 0}` using `Nat.card_congr (Equiv.subtypeEquivRight memK)`. Rewrite `h5` using `[hc]`. Conclude with `h5`.
-/
theorem orbit_sum_unfold {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A)
    (φ : H → A) (hT : ∀ h, φ h ∈ T) (hφ : ∀ a b, φ (a * b) = φ a + φ b) (R : Finset A)
    (hR : ∀ r ∈ R, r ∈ T) (hu : ∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h)
    (hK : Finite {h : H // φ h = 0}) (F : A → ℂ) (s : ℂ)
    (hs : HasSum (fun m : T => F m) s) :
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := by
  classical
  let φ' : H →* Multiplicative A := MonoidHom.mk' (fun h => Multiplicative.ofAdd (φ h))
    (fun a b => by simp [hφ])
  let K : Subgroup H := φ'.ker
  have memK : ∀ h, h ∈ K ↔ φ h = 0 := fun h => by
    simp [K, φ', MonoidHom.mem_ker]
  let bar : (H ⧸ K) → A := fun q => Multiplicative.toAdd (QuotientGroup.kerLift φ' q)
  have bar_inj : Function.Injective bar := fun a b hab =>
    QuotientGroup.kerLift_injective φ' (Multiplicative.toAdd.injective hab)
  have barT : ∀ q, bar q ∈ T := fun q => by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    exact hT h
  let ψ : (H ⧸ K) × R → T := fun p => ⟨(p.2 : A) + bar p.1, T.add_mem (hR _ p.2.2) (barT _)⟩
  have ψbij : Function.Bijective ψ := by
    constructor
    · rintro ⟨q, r, hr⟩ ⟨q', r', hr'⟩ h
      have h' : r + bar q = r' + bar q' := congrArg Subtype.val h
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
      have hm : r + φ g ∈ T := T.add_mem (hR _ hr) (hT g)
      have hrr : r = r' := (hu _ hm).unique ⟨hr, g, rfl⟩ ⟨hr', g', h'⟩
      subst hrr
      have : bar (QuotientGroup.mk g) = bar (QuotientGroup.mk g') := add_left_cancel h'
      rw [bar_inj this]
    · rintro ⟨m, hm⟩
      obtain ⟨r, ⟨hr, h, rfl⟩, -⟩ := hu m hm
      exact ⟨(QuotientGroup.mk h, ⟨r, hr⟩), rfl⟩
  have h1 : HasSum (fun p : (H ⧸ K) × R => F ((p.2 : A) + bar p.1)) s :=
    ((Equiv.ofBijective ψ ψbij).hasSum_iff (f := fun m : T => F m)).2 hs
  have h2 : HasSum (fun q : H ⧸ K => ∑ r ∈ R, F (r + bar q)) s := by
    refine h1.prod_fiberwise (fun q => ?_)
    rw [← Finset.sum_coe_sort R (fun r => F (r + bar q))]
    exact hasSum_fintype (fun r : R => F ((r : A) + bar q))
  have hKf : Finite K := Finite.of_equiv _ (Equiv.subtypeEquivRight (fun h => (memK h).symm))
  have h5 := hasSum_comp_mk K _ s h2
  have hc : Nat.card K = Nat.card {h : H // φ h = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight memK)
  rw [hc] at h5
  exact h5

end GlobalTheory.CompanionTheory.OrbitSums
