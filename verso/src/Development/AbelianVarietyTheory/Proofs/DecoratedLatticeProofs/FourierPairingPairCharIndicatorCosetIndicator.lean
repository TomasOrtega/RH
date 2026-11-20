import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts InDual)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetPairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

/- English proof (translation)
Take `⟨g, hg⟩` from `Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective`. Set `b` to `Module.Free.chooseBasis 𝒪[k] P.lat`. Set `G : (n → k) →ₗ[k] k` to `(b.extendOfIsLattice k).constr k fun i => (g (b i) : k)`. Establish `h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g` using `b.ext fun i => by`. Use `(b.extendOfIsLattice k).constr_basis k (fun i => (g (b i) : k)) i` as an intermediate fact.

Rewrite `this` using `[Module.Basis.extendOfIsLattice_apply]`. Conclude with `this`. Use `⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩` and prove the remaining obligations. Establish `h2 : G y = (g y : k)` using `LinearMap.congr_fun h1 y`. Rewrite using `[← h2, LinearMap.pi_apply_eq_sum_univ G]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`. Use `congr 2`. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem exists_lifts [DecidableEq n] (P : Pair k n) : ∃ F, Lifts P.lat F P.red := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  let b := Module.Free.chooseBasis 𝒪[k] P.lat
  let G : (n → k) →ₗ[k] k := (b.extendOfIsLattice k).constr k fun i => (g (b i) : k)
  have h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g := b.ext fun i => by
    have := (b.extendOfIsLattice k).constr_basis k (fun i => (g (b i) : k)) i
    rw [Module.Basis.extendOfIsLattice_apply] at this
    exact this
  refine ⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩
  have h2 : G y = (g y : k) := LinearMap.congr_fun h1 y
  rw [← h2, LinearMap.pi_apply_eq_sum_univ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

/- English proof (translation)
Introduce `y hy` and use `by obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩ obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩ obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self])) have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu rw [← smul_sub, smul_dotPr …`.
-/
theorem inDual_of_lifts (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F F' : n → k}
    (hF : Lifts L F f) (hF' : Lifts L F' f) : InDual L (q.inv • F - q.inv • F') := fun y hy => by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self]))
  have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu
  rw [← smul_sub, smul_dotProduct, sub_dotProduct, ← hs, ← ht, hu', smul_eq_mul, Unif.inv,
    inv_mul_cancel_left₀ q.ne_zero]
  exact u.2

/- English proof (translation)
Use `if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨F', hF', h⟩ y hy`. Use `sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)` as an intermediate fact. Rewrite `this` using `[← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel]`. Then use the resulting hypothesis.
-/
theorem cosetInd_add (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F : n → k}
    (hF : Lifts L F f) (η : n → k) : cosetInd q L f (η + q.inv • F) = dualInd L η := by
  classical
  refine if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl
  rintro ⟨F', hF', h⟩ y hy
  have := sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)
  rwa [← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel] at this

variable {χ : AddChar k Circle} (hχ : HasConductor χ 1) {e : k}

include hχ in

/- English proof (translation)
Break down `he with rfl | rfl` into its components or cases. Simplify using `using apply_int_eq_one hχ ⟨_, hη y hy⟩`. Simplify using `using apply_int_eq_one hχ (-⟨_, hη y hy⟩)`.
-/
theorem char_dual (he : e = 1 ∨ e = -1) {L : Submodule 𝒪[k] (n → k)} {η y : n → k} (hη : InDual L η) (hy : y ∈ L) :
    χ (e * (η ⬝ᵥ y)) = 1 := by
  rcases he with rfl | rfl
  · simpa using apply_int_eq_one hχ ⟨_, hη y hy⟩
  · simpa using apply_int_eq_one hχ (-⟨_, hη y hy⟩)

/- English proof (translation)
Take `⟨s, hs, hr⟩` from `hF ⟨y, hy⟩`. Establish `hr' : P.ev y = residue 𝒪[k] s` using `((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm`. Rewrite using `[add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul, smul_dotProduct, ← hs, hr']`. Break down `he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Simplify using `[resChar_residue]`.

Use `resChar_residue hχ q (-s)` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem char_coset (q : Unif k) {ε : 𝓀[k]ˣ} (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) {P : Pair k n} {F η y : n → k}
    (hF : Lifts P.lat F P.red) (hη : InDual P.lat η) (hy : y ∈ P.lat) :
    (χ (e * ((η + q.inv • F) ⬝ᵥ y)) : ℂ) = resChar χ hχ q (ε * P.ev y) := by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  have hr' : P.ev y = residue 𝒪[k] s := ((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm
  rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul,
    smul_dotProduct, ← hs, hr']
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [resChar_residue]
  · have := resChar_residue hχ q (-s)
    simpa using this.symm

/- English proof (translation)
Apply the tactic sequence `have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hne (Pair.ext fun x a => ?_)` and prove the remaining obligations.

Rewrite using `[Pair.dia_hasVal, hi]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx'` using `h ▸ hx.mem`. Use `hc x hx'` as an intermediate fact.

Rewrite `this` using `[hx.ev_eq, neg_add_eq_zero]`. Conclude with `this ▸ Pair.hasVal_ev hx'`. Introduce `hx`. Use `hc x hx.mem` as an intermediate fact. Rewrite `this` using `[hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj]`.

Conclude with `this ▸ Pair.hasVal_ev (h ▸ hx.mem)`. Take `⟨a, ha⟩` from `AddChar.ne_one_iff.1 (resChar_ne_one hχ q)`. Take `⟨s, hs⟩` from `residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)`. Use `⟨s • y, Q.lat.smul_mem s hy, ?_⟩` and prove the remaining obligations. Rewrite using `[((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]`.

Use `ha using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← inv_mul_cancel_right₀ hc a, ← hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_char_ne (q : Unif k) {ε : 𝓀[k]ˣ} (hε : ε = 1 ∨ ε = -1) {Q Q'' : Pair k n} (h : Q''.lat = Q.lat)
    (hne : Q'' ≠ ε • Q) : ∃ y ∈ Q.lat, resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ≠ 1 := by
  have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hne (Pair.ext fun x a => ?_)
    rw [Pair.dia_hasVal, hi]
    constructor
    · intro hx
      have hx' := h ▸ hx.mem
      have := hc x hx'
      rw [hx.ev_eq, neg_add_eq_zero] at this
      exact this ▸ Pair.hasVal_ev hx'
    · intro hx
      have := hc x hx.mem
      rw [hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj] at this
      exact this ▸ Pair.hasVal_ev (h ▸ hx.mem)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 (resChar_ne_one hχ q)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)
  refine ⟨s • y, Q.lat.smul_mem s hy, ?_⟩
  rw [((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]
  convert ha using 2
  rw [← inv_mul_cancel_right₀ hc a, ← hs]
  ring

/- English proof (translation)
Use `haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k`. Use `haveI := secondCountable k`. Take `⟨F, hF⟩` from `exists_lifts Q''`. Establish `hε : ε = 1 ∨ ε = -1` using `he.imp And.right And.right`. Establish `key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ`.

Unfold `fpair`. Rewrite using `[← integral_add_right_eq_self _ (q.inv • F)]`. Use `congr 1`. Use function extensionality and compare the values at `η`. Rewrite using `[cosetInd_add q hF, h]`.

Distinguish the cases in `hη : InDual Q.lat η`. Use `swap`. Rewrite using `[dualInd, if_neg hη, mul_zero, mul_zero]`. Use `congr 2`. Use function extensionality and compare the values at `y`.

Distinguish the cases in `hy : y ∈ Q.lat`. Rewrite using `[char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Unfold `fpair`. Use `congr 1`. Use function extensionality and compare the values at `η`.

Distinguish the cases in `hη : InDual Q.lat η`. Use `swap`. Rewrite using `[dualInd, if_neg hη, mul_zero, mul_zero]`. Use `congr 2`. Use function extensionality and compare the values at `y`.

Distinguish the cases in `hy : y ∈ Q.lat`. Establish `h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y` using `(Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq`. Apply the tactic sequence `have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp`. Rewrite `h1` using `[hi]`. Rewrite using `[char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]`.

Simplify using the standard rewrite rules. Rewrite using `[vecInd, if_neg hy, zero_mul, zero_mul]`. Introduce `hne`. Take `⟨y₀, hy₀, hc⟩` from `exists_char_ne hχ q hε h hne`. Establish `e1` using `integral_add_right_eq_self (μ := μ) (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀`.

Establish `e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) = resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y))` using `fun y => by`. Distinguish the cases in `hy : y ∈ Q.lat`. Rewrite using `[vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul, ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]`. Simplify using the standard rewrite rules. Simplify using `only [e2] at e1`. Rewrite `e1` using `[integral_const_mul]`. Establish `h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hc ((mul_eq_right₀ h0).1 e1)`. Simplify using `[h0]`.
-/
theorem fpair_charInd_cosetInd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ) (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (Q Q'' : Pair k n) (h : Q''.lat = Q.lat) :
    (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧
    (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  obtain ⟨F, hF⟩ := exists_lifts Q''
  have hε : ε = 1 ∨ ε = -1 := he.imp And.right And.right
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ := by
    unfold fpair
    rw [← integral_add_right_eq_self _ (q.inv • F)]
    congr 1
    funext η
    rw [cosetInd_add q hF, h]
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · rw [char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]
      ring
    · rw [charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]
  rw [key]
  constructor
  · rintro rfl
    unfold fpair
    congr 1
    funext η
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · have h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y := (Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq
      have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
      rw [hi] at h1
      rw [char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]
      simp
    · rw [vecInd, if_neg hy, zero_mul, zero_mul]
  · intro hne
    obtain ⟨y₀, hy₀, hc⟩ := exists_char_ne hχ q hε h hne
    have e1 := integral_add_right_eq_self (μ := μ)
      (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀
    have e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) =
        resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) := fun y => by
      by_cases hy : y ∈ Q.lat
      · rw [vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul,
          ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq,
          ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]
        congr 1
        ring
      · rw [vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]
        simp
    simp only [e2] at e1
    rw [integral_const_mul] at e1
    have h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0 := by
      by_contra h0
      exact hc ((mul_eq_right₀ h0).1 e1)
    simp [h0]

end GlobalTheory.FinPl.CosetPairing

end
