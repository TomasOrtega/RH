import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftHermitianIsometryModLevelSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulMemOfMemSpan

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.RepTrivial

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def red (E : Type) [Field E] (n M : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] StdMod E n M :=
  LinearMap.pi fun j => (Ideal.Quotient.mkₐ (𝓞 E) (Ideal.span {(M : 𝓞 E)})).toLinearMap ∘ₗ LinearMap.proj j

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem red_apply (M : ℕ) (x : Fin n → 𝓞 E) (j : Fin n) : red E n M x j = Ideal.Quotient.mk _ (x j) := rfl

omit [NumberField E] in
/- English proof (translation)
Introduce `y` and use `by choose x hx using fun j => Ideal.Quotient.mk_surjective (y j) exact ⟨x, funext hx⟩`.
-/
theorem red_surjective (M : ℕ) : Function.Surjective (red E n M) := fun y => by
  choose x hx using fun j => Ideal.Quotient.mk_surjective (y j)
  exact ⟨x, funext hx⟩

omit [NumberField E] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ∀ j, ∃ a : 𝓞 E, a * (M : 𝓞 E) = x j - y j` using `fun j => Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun h j))`. Use `choose z hz using h1`. Use `⟨z, funext fun j => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `x j = y j + M • z j`. Rewrite using `[nsmul_eq_mul]`. Take the linear combination `-hz j`. Introduce and unpack `⟨z, rfl⟩`. Use function extensionality and compare the values at `j`.

Use `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨z j, ?_⟩)` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem red_eq_iff (M : ℕ) (x y : Fin n → 𝓞 E) : red E n M x = red E n M y ↔ ∃ z, x = y + M • z := by
  constructor
  · intro h
    have h1 : ∀ j, ∃ a : 𝓞 E, a * (M : 𝓞 E) = x j - y j := fun j =>
      Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun h j))
    choose z hz using h1
    refine ⟨z, funext fun j => ?_⟩
    change x j = y j + M • z j
    rw [nsmul_eq_mul]
    linear_combination -hz j
  · rintro ⟨z, rfl⟩
    funext j
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨z j, ?_⟩)
    simp [mul_comm]

def inc (E : Type) [Field E] [NumberField E] (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] stdLat E n where
  toFun x := ⟨fun j => (x j : E), fun j _ => Submodule.mem_one.2 ⟨x j, rfl⟩⟩
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp [Algebra.smul_def]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inc_apply (x : Fin n → 𝓞 E) (j : Fin n) : (inc E n x : Fin n → E) j = x j := rfl

/- English proof (translation)
Introduce `x y h` and use `funext fun j => RingOfIntegers.ext (congrFun (congrArg Subtype.val h) j)`.
-/
theorem inc_injective : Function.Injective (inc E n) := fun x y h =>
  funext fun j => RingOfIntegers.ext (congrFun (congrArg Subtype.val h) j)

/- English proof (translation)
Introduce `v` and use `by choose x hx using fun j => Submodule.mem_one.1 (v.2 j (Set.mem_univ j)) exact ⟨x, Subtype.ext (funext hx)⟩`.
-/
theorem inc_surjective : Function.Surjective (inc E n) := fun v => by
  choose x hx using fun j => Submodule.mem_one.1 (v.2 j (Set.mem_univ j))
  exact ⟨x, Subtype.ext (funext hx)⟩

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL`. Use `haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Flat (𝓞 E) L := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem projective_of_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) : Module.Projective (𝓞 E) L := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat (𝓞 E) L := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Rewrite using `[← Module.Finite.iff_fg]`. Conclude with `Module.Finite.of_surjective _ inc_surjective`.
-/
theorem std_fg : (stdLat E n).FG := by
  rw [← Module.Finite.iff_fg]
  exact Module.Finite.of_surjective _ inc_surjective

/- English proof (translation)
Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `using GlobalTheory.UnRep.StdInhab.single_mem n j`.
-/
theorem std_span : Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  simpa using GlobalTheory.UnRep.StdInhab.single_mem n j

variable [IsCMField E]

/- English proof (translation)
Take `⟨k, rfl⟩` from `hd`. Use `haveI := projective_of_fg Λ.La (GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU).1`. Take `⟨io', h1, h2⟩` from `GlobalTheory.T.exists_lift_hermitianIsometryModLevel_selfDual E n M hur hM Λ _ hU hf k (Nat.pos_of_mul_pos_left hM')`. Take `⟨f', hf'⟩` from `Module.projective_lifting_property (red E n (M * k)) io' (red_surjective _)`. Use `⟨f', hf' ▸ h1, fun a => (red_eq_iff _ _ _).1 (funext fun j => ?_)⟩` and prove the remaining obligations.

Conclude with `(h2 a (f' a) (fun j => by rw [← hf', LinearMap.comp_apply, red_apply]) j).symm`.
-/
theorem step (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Λ : GenLat E n) (hU : Λ.Unimod)
    {M M' : ℕ} (hM : 0 < M) (hM' : 0 < M') (hd : M ∣ M') (f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E))
    (hf : IsIsomMod Λ M (red E n M ∘ₗ f)) :
    ∃ f' : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E), IsIsomMod Λ M' (red E n M' ∘ₗ f') ∧ ∀ a, ∃ z, f' a = f a + M • z := by
  obtain ⟨k, rfl⟩ := hd
  haveI := projective_of_fg Λ.La (GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU).1
  obtain ⟨io', h1, h2⟩ := GlobalTheory.T.exists_lift_hermitianIsometryModLevel_selfDual E n M hur hM Λ _ hU hf k (Nat.pos_of_mul_pos_left hM')
  obtain ⟨f', hf'⟩ := Module.projective_lifting_property (red E n (M * k)) io' (red_surjective _)
  refine ⟨f', hf' ▸ h1, fun a => (red_eq_iff _ _ _).1 (funext fun j => ?_)⟩
  exact (h2 a (f' a) (fun j => by rw [← hf', LinearMap.comp_apply, red_apply]) j).symm

/- English proof (translation)
Use `haveI := projective_of_fg Λ.La (GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU).1`. Take `⟨f₀, hf₀⟩` from `Module.projective_lifting_property (red E n m) io (red_surjective _)`. Establish `hpos : ∀ j : ℕ, 0 < m * j.factorial` using `fun j => Nat.mul_pos hm j.factorial_pos`. Establish `h0 : IsIsomMod Λ (m * Nat.factorial 0) (red E n (m * Nat.factorial 0) ∘ₗ f₀)`. Establish `: ∀ M, M = m → IsIsomMod Λ M (red E n M ∘ₗ f₀)`.

Introduce and unpack `_ rfl`. Conclude with `hf₀ ▸ hio`. Conclude with `this _ (by simp)`. Use `choose st h1 h2 using fun (j : ℕ) (f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E)) (hf : IsIsomMod Λ (m * j.factorial) (red E n (m * j.factorial) ∘ₗ f)) => step hur Λ hU (hpos j) (hpos (j + 1)) (Nat.mul_dvd_mul_left m (Nat.factorial_dvd_factorial j.le_succ)) f hf`. Set `s : ∀ j : ℕ, {f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E) // IsIsomMod Λ (m * j.factorial) (red E n (m * j.factorial) ∘ₗ f)}` to `fun j => Nat.rec ⟨f₀, h0⟩ (fun j p => ⟨st j p.1 p.2, h1 j p.1 p.2⟩) j`.

Use `⟨fun j => (s j).1, hf₀, fun j => (s j).2, fun i j hij a => ?_⟩` and prove the remaining obligations. Proceed by induction on `j, hij using Nat.le_induction with`. Consider the case `base => exact ⟨0, by simp⟩`. Consider the case `succ j hij ih`. Take `⟨z, hz⟩` from `ih`.

Take `⟨w, hw⟩` from `h2 j (s j).1 (s j).2 a`. Take `⟨c, hc⟩` from `Nat.factorial_dvd_factorial hij`. Use `⟨z + c • w, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `st j (s j).1 (s j).2 a = _`. Rewrite using `[hw, smul_add, smul_smul, mul_assoc, ← hc, ← add_assoc]`.

Conclude with `congrArg (· + _) hz`.
-/
theorem exists_tower (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Λ : GenLat E n)
    (hU : Λ.Unimod) {m : ℕ} (hm : 0 < m) (io : Λ.La →ₗ[𝓞 E] StdMod E n m) (hio : IsIsomMod Λ m io) :
    ∃ f : ℕ → (Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E)), red E n m ∘ₗ f 0 = io ∧
      (∀ j : ℕ, IsIsomMod Λ (m * j.factorial) (red E n (m * j.factorial) ∘ₗ f j)) ∧
      ∀ i j : ℕ, i ≤ j → ∀ a, ∃ z, f j a = f i a + (m * i.factorial) • z := by
  haveI := projective_of_fg Λ.La (GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU).1
  obtain ⟨f₀, hf₀⟩ := Module.projective_lifting_property (red E n m) io (red_surjective _)
  have hpos : ∀ j : ℕ, 0 < m * j.factorial := fun j => Nat.mul_pos hm j.factorial_pos
  have h0 : IsIsomMod Λ (m * Nat.factorial 0) (red E n (m * Nat.factorial 0) ∘ₗ f₀) := by
    have : ∀ M, M = m → IsIsomMod Λ M (red E n M ∘ₗ f₀) := by
      rintro _ rfl
      exact hf₀ ▸ hio
    exact this _ (by simp)
  choose st h1 h2 using fun (j : ℕ) (f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E))
    (hf : IsIsomMod Λ (m * j.factorial) (red E n (m * j.factorial) ∘ₗ f)) =>
    step hur Λ hU (hpos j) (hpos (j + 1))
      (Nat.mul_dvd_mul_left m (Nat.factorial_dvd_factorial j.le_succ)) f hf
  let s : ∀ j : ℕ, {f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E) //
      IsIsomMod Λ (m * j.factorial) (red E n (m * j.factorial) ∘ₗ f)} :=
    fun j => Nat.rec ⟨f₀, h0⟩ (fun j p => ⟨st j p.1 p.2, h1 j p.1 p.2⟩) j
  refine ⟨fun j => (s j).1, hf₀, fun j => (s j).2, fun i j hij a => ?_⟩
  induction j, hij using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ j hij ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := h2 j (s j).1 (s j).2 a
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hij
    refine ⟨z + c • w, ?_⟩
    change st j (s j).1 (s j).2 a = _
    rw [hw, smul_add, smul_smul, mul_assoc, ← hc, ← add_assoc]
    exact congrArg (· + _) hz

/- English proof (translation)
Take `⟨hs, hk, -⟩` from `hf`. Establish `hs' : ∀ x, ∃ a z, x = f a + (N * k) • z` using `fun x => by`. Take `⟨a, ha⟩` from `hs (red E n _ x)`. Take `⟨z, hz⟩` from `(red_eq_iff _ _ _).1 (Eq.symm ha)`. Conclude with `⟨a, z, hz⟩`.

Use `⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨v, hv⟩`. Take `⟨x, rfl⟩` from `inc_surjective v`. Establish `h1 : f a = N • x` using `inc_injective (by rw [map_nsmul]; exact hv)`. Take `⟨b, z, hb⟩` from `hs' x`.

Establish `h2 : (red E n (N * k) ∘ₗ f) (a - N • b) = 0`. Rewrite using `[← (red E n (N * k)).map_zero]`. Use `(red_eq_iff _ _ _).2 ⟨N • z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_nsmul, h1, hb, smul_add, smul_comm N (N * k)]`. Normalize the expressions using the abelian group laws.

Take `⟨u, hu, e⟩` from `(hk _).1 h2`. Use `⟨b + k • ⟨u, hu⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite `e` using `[Nat.cast_smul_eq_nsmul]`. Simplify using `only [Submodule.coe_sub, AddSubmonoidClass.coe_nsmul] at e`. Simplify using `only [Submodule.coe_add, AddSubmonoidClass.coe_nsmul, smul_add, smul_smul, ← e]`.

Normalize the expressions using the abelian group laws. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨_, map_nsmul _ _ _⟩`. Take `⟨x, rfl⟩` from `inc_surjective a'`. Take `⟨a, z, e⟩` from `hs' x`.

Use `⟨a, inc E n (k • z), ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_add, mul_smul, map_nsmul]`. Both sides reduce to the same expression.
-/
theorem iso_mod (Λ : GenLat E n) {N k : ℕ} (f : Λ.La →ₗ[𝓞 E] (Fin n → 𝓞 E))
    (hf : IsIsomMod Λ (N * k) (red E n (N * k) ∘ₗ f)) :
    (∀ a, (∃ v, (inc E n ∘ₗ f) a = N • v) ↔ ∃ v, a = N • v) ∧
      ∀ a', ∃ a v, a' = (inc E n ∘ₗ f) a + N • v := by
  obtain ⟨hs, hk, -⟩ := hf
  have hs' : ∀ x, ∃ a z, x = f a + (N * k) • z := fun x => by
    obtain ⟨a, ha⟩ := hs (red E n _ x)
    obtain ⟨z, hz⟩ := (red_eq_iff _ _ _).1 (Eq.symm ha)
    exact ⟨a, z, hz⟩
  refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
  · rintro ⟨v, hv⟩
    obtain ⟨x, rfl⟩ := inc_surjective v
    have h1 : f a = N • x := inc_injective (by rw [map_nsmul]; exact hv)
    obtain ⟨b, z, hb⟩ := hs' x
    have h2 : (red E n (N * k) ∘ₗ f) (a - N • b) = 0 := by
      rw [← (red E n (N * k)).map_zero]
      refine (red_eq_iff _ _ _).2 ⟨N • z, ?_⟩
      rw [map_sub, map_nsmul, h1, hb, smul_add, smul_comm N (N * k)]
      abel
    obtain ⟨u, hu, e⟩ := (hk _).1 h2
    refine ⟨b + k • ⟨u, hu⟩, Subtype.ext ?_⟩
    rw [Nat.cast_smul_eq_nsmul] at e
    simp only [Submodule.coe_sub, AddSubmonoidClass.coe_nsmul] at e
    simp only [Submodule.coe_add, AddSubmonoidClass.coe_nsmul, smul_add, smul_smul, ← e]
    abel
  · rintro ⟨v, rfl⟩
    exact ⟨_, map_nsmul _ _ _⟩
  · obtain ⟨x, rfl⟩ := inc_surjective a'
    obtain ⟨a, z, e⟩ := hs' x
    refine ⟨a, inc E n (k • z), ?_⟩
    rw [e, map_add, mul_smul, map_nsmul]
    rfl

/- English proof (translation)
The claim follows from `GlobalTheory.UnRep.StdInhab.hermE_one (IsCMField.complexConj E) x y`.
-/
theorem sum_one (x y : Fin n → E) :
    ∑ a, ∑ b, x a * (1 : Matrix (Fin n) (Fin n) E) a b * IsCMField.complexConj E (y b) =
      ∑ a, x a * IsCMField.complexConj E (y a) :=
  GlobalTheory.UnRep.StdInhab.hermE_one (IsCMField.complexConj E) x y

/- English proof (translation)
Take `⟨f, h0, hiso, hcomp⟩` from `exists_tower hur Λ hU hm io hio`. Take `⟨hfg, hsp⟩` from `GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU`. Establish `hfac : ∀ N : ℕ, 0 < N → ∃ k, m * N.factorial = N * k` using `fun N hN => Dvd.dvd.mul_left (Nat.dvd_factorial hN le_rfl) m`. Take `⟨g, hg1, hg2, hg3⟩` from `exists_adelic_matrix_of_tower (maximalRealSubfield E) E n Λ.La (stdLat E n) (fun N => inc E n ∘ₗ f N) hfg hsp std_fg std_span (fun N k hN hk a => by`. Take `⟨z, hz⟩` from `hcomp N (N * k) (Nat.le_mul_of_pos_right N hk) a`.

Take `⟨c, hc⟩` from `hfac N hN`. Use `⟨inc E n (c • z), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hz, hc, map_add, mul_smul, map_nsmul])`. Use the proof step `(fun N hN => by`. Take `⟨c, hc⟩` from `hfac N hN`.

Use `hiso N` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `iso_mod Λ _ this)`. Use `⟨g, hg1, hg3 (IsCMField.complexConj E) 1 1 (fun x hx y hy => ?_) fun N hN x y => ?_, fun v x hx => ?_⟩` and prove the remaining obligations. Take `⟨x, hx'⟩` from `inc_surjective ⟨x, hx⟩`.

Take `⟨y, hy'⟩` from `inc_surjective ⟨y, hy⟩`. Consider the cases of `hx'`. Consider the cases of `hy'`. Rewrite using `[sum_one, FractionalIdeal.mem_one_iff]`. Use `⟨∑ a, x a * IsCMField.ringOfIntegersComplexConj E (y a), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]`. Take `⟨c, hc⟩` from `hfac N hN`. Take `⟨b, hb⟩` from `(hiso N).2.2 x y (f N x) (f N y) (fun _ => rfl) fun _ => rfl`.

Use `⟨((-(c * b) : 𝓞 E) : E), (FractionalIdeal.mem_one_iff _).2 ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_one, sum_one, nsmul_eq_mul]`. Rewrite `hb` using `[hc]`. Simplify using `only [LinearMap.comp_apply, inc_apply]`. Move the coercions through the operations in `at hb ⊢`.

Take the linear combination `-hb`. Take `⟨w, hw, e⟩` from `hg2 m hm v`. Take `⟨z, hz⟩` from `hcomp 0 m (Nat.zero_le m) v`. Take `⟨z', hz'⟩` from `(red_eq_iff m (f 0 v) x).1 (by rw [← hx, ← h0]; rfl)`. Use `⟨fv _ (inc E n (z' + z) : Fin n → E) + w, add_mem (cap_fv_mem _ _ _ (inc E n _).2) hw, ?_⟩` and prove the remaining obligations.

Establish `e1 : f m v = x + m • (z' + z)`. Rewrite using `[hz, hz', smul_add, add_assoc]`. Simplify using the standard rewrite rules. Rewrite using `[e, LinearMap.comp_apply, e1, map_add, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul, cap_fv_add, cap_fv_nsmul, smul_add, add_assoc]`. Both sides reduce to the same expression.
-/
theorem exists_adelic (hur : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Λ : GenLat E n)
    (hU : Λ.Unimod) {m : ℕ} (hm : 0 < m) (io : Λ.La →ₗ[𝓞 E] StdMod E n m) (hio : IsIsomMod Λ m io) :
    ∃ g : GL (Fin n) (RA (maximalRealSubfield E) E),
      g.1.mulVec '' (hat (maximalRealSubfield E) (Λ.La : Set (Fin n → E))) =
        hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)) ∧
      GlobalTheory.UnRep.IsUnA (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) g.1 ∧
      ∀ (v : Λ.La) (x : Fin n → 𝓞 E), io v = red E n m x →
        ∃ w ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
          g.1 *ᵥ fv (maximalRealSubfield E) (v : Fin n → E) =
            fv (maximalRealSubfield E) (fun j => (x j : E)) + m • w := by
  obtain ⟨f, h0, hiso, hcomp⟩ := exists_tower hur Λ hU hm io hio
  obtain ⟨hfg, hsp⟩ := GlobalTheory.GenusLatCompare.isLat_of_unimod Λ hU
  have hfac : ∀ N : ℕ, 0 < N → ∃ k, m * N.factorial = N * k := fun N hN =>
    Dvd.dvd.mul_left (Nat.dvd_factorial hN le_rfl) m
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_adelic_matrix_of_tower (maximalRealSubfield E) E n Λ.La (stdLat E n)
    (fun N => inc E n ∘ₗ f N) hfg hsp std_fg std_span
    (fun N k hN hk a => by
      obtain ⟨z, hz⟩ := hcomp N (N * k) (Nat.le_mul_of_pos_right N hk) a
      obtain ⟨c, hc⟩ := hfac N hN
      refine ⟨inc E n (c • z), ?_⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hz, hc, map_add, mul_smul, map_nsmul])
    (fun N hN => by
      obtain ⟨c, hc⟩ := hfac N hN
      have := hiso N
      rw [hc] at this
      exact iso_mod Λ _ this)
  refine ⟨g, hg1, hg3 (IsCMField.complexConj E) 1 1 (fun x hx y hy => ?_) fun N hN x y => ?_, fun v x hx => ?_⟩
  · obtain ⟨x, hx'⟩ := inc_surjective ⟨x, hx⟩
    obtain ⟨y, hy'⟩ := inc_surjective ⟨y, hy⟩
    cases hx'
    cases hy'
    rw [sum_one, FractionalIdeal.mem_one_iff]
    refine ⟨∑ a, x a * IsCMField.ringOfIntegersComplexConj E (y a), ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, ← IsCMField.coe_ringOfIntegersComplexConj]
  · obtain ⟨c, hc⟩ := hfac N hN
    obtain ⟨b, hb⟩ := (hiso N).2.2 x y (f N x) (f N y) (fun _ => rfl) fun _ => rfl
    refine ⟨((-(c * b) : 𝓞 E) : E), (FractionalIdeal.mem_one_iff _).2 ⟨_, rfl⟩, ?_⟩
    rw [sum_one, sum_one, nsmul_eq_mul]
    rw [hc] at hb
    simp only [LinearMap.comp_apply, inc_apply]
    push_cast at hb ⊢
    linear_combination -hb
  · obtain ⟨w, hw, e⟩ := hg2 m hm v
    obtain ⟨z, hz⟩ := hcomp 0 m (Nat.zero_le m) v
    obtain ⟨z', hz'⟩ := (red_eq_iff m (f 0 v) x).1 (by rw [← hx, ← h0]; rfl)
    refine ⟨fv _ (inc E n (z' + z) : Fin n → E) + w, add_mem (cap_fv_mem _ _ _ (inc E n _).2) hw, ?_⟩
    have e1 : f m v = x + m • (z' + z) := by
      rw [hz, hz', smul_add, add_assoc]
      simp
    rw [e, LinearMap.comp_apply, e1, map_add, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
      cap_fv_add, cap_fv_nsmul, smul_add, add_assoc]
    rfl

section Adelic

variable (F : Type) {K : Type} [Field F] [NumberField F] [Field K] [Algebra F K]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [fv, GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]`.
-/
theorem fv_mulVec (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    fv F (γ *ᵥ v) = GlobalTheory.UnRep.fm F γ *ᵥ fv F v := by
  funext i
  simp only [fv, GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fv, TensorProduct.tmul_sub]`.
-/
theorem fv_sub (x y : Fin n → K) : fv F (x - y) = fv F x - fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_sub]

end Adelic

/- English proof (translation)
Introduce `E _ _ _ n hur m bad hm hbad Λ io hU hio`. Take `⟨g, hg1, hg2, hg3⟩` from `exists_adelic hur Λ hU hm io hio`. Establish `hinv : ∀ z, (g⁻¹).1 *ᵥ (g.1 *ᵥ z) = z` using `fun z => by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hinv' : ∀ z, g.1 *ᵥ ((g⁻¹).1 *ᵥ z) = z` using `fun z => by`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hherm : GlobalTheory.UnRep.IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E)` using `⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => by`. Simplify using `[Matrix.one_apply, eq_comm], by simp⟩`. Take `⟨γ, hγ, t, ht, hc⟩` from `GlobalTheory.T.unitaryGroup_weak_approximation_at_primes (maximalRealSubfield E) E (IsCMField.complexConj E) n 1 hherm (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (stdLat E n) std_fg std_span g⁻¹ (m * bad) m (fun x y => by rw [← hg2, hinv', hinv']) (Nat.mul_pos hm hbad) hm`. Establish `hrat` using `(hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) std_fg std_span).1`.

Establish `hgv : ∀ v ∈ Λ.La, g.1 *ᵥ fv (maximalRealSubfield E) v ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E))` using `fun v hv => by`. Rewrite using `[← SetLike.mem_coe, ← hg1]`. Conclude with `⟨_, cap_fv_mem _ _ v hv, rfl⟩`. Establish `key : ∀ v ∈ Λ.La, ∃ w ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)), t • fv (maximalRealSubfield E) (γ.1 *ᵥ v) = t • (g.1 *ᵥ fv (maximalRealSubfield E) v) + m • w`. Introduce `v hv`.

Take `⟨w, hw, e⟩` from `hc _ (hgv v hv)`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← Matrix.mulVec_mulVec, hinv, ← fv_mulVec, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `h1 : ∀ v ∈ Λ.La, t • γ.1 *ᵥ v ∈ stdLat E n` using `fun v hv => by`.

Take `⟨w, hw, e⟩` from `key v hv`. Rewrite using `[← hrat, cap_fv_nsmul, e]`. Conclude with `add_mem (nsmul_mem (hgv v hv) _) (nsmul_mem hw _)`. Establish `h2 : ∀ x ∈ stdLat E n, t • x ∈ (actLat γ.1 Λ).La` using `fun x hx => by`. Establish `hx' : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ (t • x)) = t • x`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Use `⟨(γ⁻¹).1 *ᵥ (t • x), (hU _).2 fun w hw => ?_, hx'⟩` and prove the remaining obligations. Establish `e` using `hγ w ((γ⁻¹).1 *ᵥ (t • x))`. Rewrite `e` using `[hx', GlobalTheory.UnRep.StdInhab.hermE_one, GlobalTheory.UnRep.StdInhab.hermE_one]`. Take `⟨a, ha⟩` from `inc_surjective ⟨_, h1 w hw⟩`.

Take `⟨b, hb⟩` from `inc_surjective ⟨_, hx⟩`. Use `⟨∑ j, a j * IsCMField.ringOfIntegersComplexConj E (b j), ?_⟩` and prove the remaining obligations. Simplify using `only [mul_comm (IsCMField.complexConj E _)]`. Rewrite using `[← e, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `ha' : (a j : E) = t • (γ.1 *ᵥ w) j` using `congrFun (congrArg Subtype.val ha) j`. Establish `hb' : (b j : E) = x j` using `congrFun (congrArg Subtype.val hb) j`. Rewrite using `[map_mul]`. Express the relevant statement in the definitionally equal form `(a j : E) * ((IsCMField.ringOfIntegersComplexConj E (b j) : 𝓞 E) : E) = _`. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, ha', hb', Pi.smul_apply, map_nsmul, smul_mul_assoc, mul_smul_comm]`.

Establish `htriv : ∀ s, t.Coprime s → (actLat γ.1 Λ).TrivAt s` using `fun s hs => ⟨t, hs, (GlobalTheory.GenusLatCompare.span_smul_le_iff _ _ _).2 (by`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `h1 v hv), (GlobalTheory.GenusLatCompare.span_smul_le_iff _ _ _).2 h2⟩`. Use `⟨γ.1, ?_, htriv _ ht.coprime_mul_left_right, htriv _ ht.coprime_mul_right_right, fun v x hx => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← (GlobalTheory.UnRep.StdInhab.isUnE_one_iff _ _).1 hγ i j]`. Both sides reduce to the same expression. Take `⟨w, hw, e⟩` from `key v v.2`. Take `⟨w', hw', e'⟩` from `hg3 v x (funext hx)`. Establish `hME : (m : E) ≠ 0` using `by exact_mod_cast hm.ne'`.

Use `set u : Fin n → E := (m : E)⁻¹ • (t • (γ.1 *ᵥ (v : Fin n → E) - fun j => (x j : E))) with hu`. Establish `hmu : m • u = t • (γ.1 *ᵥ (v : Fin n → E) - fun j => (x j : E))`. Rewrite using `[hu, ← Nat.cast_smul_eq_nsmul E m, smul_smul, mul_inv_cancel₀ hME, one_smul]`. Establish `e2 : fv (maximalRealSubfield E) u = t • w' + w`. Use `lim_nsmul_cancel (maximalRealSubfield E) hm ?_` and prove the remaining obligations.

Rewrite using `[← cap_fv_nsmul, hmu, cap_fv_nsmul, fv_sub, smul_sub, e, e', smul_add, smul_add, smul_comm t m]`. Normalize the expressions using the abelian group laws. Establish `hu' : u ∈ stdLat E n`. Rewrite using `[← hrat, e2]`. Conclude with `add_mem (nsmul_mem hw' _) hw`.

Take `⟨b, hb⟩` from `inc_surjective ⟨_, hu'⟩`. Use `⟨t, ht.coprime_mul_right_right, fun j => ⟨b j, ?_⟩⟩` and prove the remaining obligations. Establish `hb' : (b j : E) = u j` using `congrFun (congrArg Subtype.val hb) j`. Use `congrFun hmu j` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul] at this`.

Rewrite using `[hb']`. Conclude with `this.symm`.
-/
theorem repExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), RepExists E n := by
  intro E _ _ _ n hur m bad hm hbad Λ io hU hio
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_adelic hur Λ hU hm io hio
  have hinv : ∀ z, (g⁻¹).1 *ᵥ (g.1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ z, g.1 *ᵥ ((g⁻¹).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hherm : GlobalTheory.UnRep.IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) :=
    ⟨IsCMField.complexConj_apply_apply E, IsCMField.complexConj_ne_one E, fun a b => by
      simp [Matrix.one_apply, eq_comm], by simp⟩
  obtain ⟨γ, hγ, t, ht, hc⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes (maximalRealSubfield E) E (IsCMField.complexConj E) n 1 hherm
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (stdLat E n) std_fg std_span g⁻¹ (m * bad) m
    (fun x y => by rw [← hg2, hinv', hinv']) (Nat.mul_pos hm hbad) hm
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) std_fg std_span).1
  have hgv : ∀ v ∈ Λ.La, g.1 *ᵥ fv (maximalRealSubfield E) v ∈
      hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)) := fun v hv => by
    rw [← SetLike.mem_coe, ← hg1]
    exact ⟨_, cap_fv_mem _ _ v hv, rfl⟩
  have key : ∀ v ∈ Λ.La, ∃ w ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      t • fv (maximalRealSubfield E) (γ.1 *ᵥ v) = t • (g.1 *ᵥ fv (maximalRealSubfield E) v) + m • w := by
    intro v hv
    obtain ⟨w, hw, e⟩ := hc _ (hgv v hv)
    refine ⟨w, hw, ?_⟩
    rw [← e, ← Matrix.mulVec_mulVec, hinv, ← fv_mulVec, smul_sub]
    abel
  have h1 : ∀ v ∈ Λ.La, t • γ.1 *ᵥ v ∈ stdLat E n := fun v hv => by
    obtain ⟨w, hw, e⟩ := key v hv
    rw [← hrat, cap_fv_nsmul, e]
    exact add_mem (nsmul_mem (hgv v hv) _) (nsmul_mem hw _)
  have h2 : ∀ x ∈ stdLat E n, t • x ∈ (actLat γ.1 Λ).La := fun x hx => by
    have hx' : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ (t • x)) = t • x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨(γ⁻¹).1 *ᵥ (t • x), (hU _).2 fun w hw => ?_, hx'⟩
    have e := hγ w ((γ⁻¹).1 *ᵥ (t • x))
    rw [hx', GlobalTheory.UnRep.StdInhab.hermE_one, GlobalTheory.UnRep.StdInhab.hermE_one] at e
    obtain ⟨a, ha⟩ := inc_surjective ⟨_, h1 w hw⟩
    obtain ⟨b, hb⟩ := inc_surjective ⟨_, hx⟩
    refine ⟨∑ j, a j * IsCMField.ringOfIntegersComplexConj E (b j), ?_⟩
    simp only [mul_comm (IsCMField.complexConj E _)]
    rw [← e, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha' : (a j : E) = t • (γ.1 *ᵥ w) j := congrFun (congrArg Subtype.val ha) j
    have hb' : (b j : E) = x j := congrFun (congrArg Subtype.val hb) j
    rw [map_mul]
    change (a j : E) * ((IsCMField.ringOfIntegersComplexConj E (b j) : 𝓞 E) : E) = _
    rw [IsCMField.coe_ringOfIntegersComplexConj, ha', hb', Pi.smul_apply, map_nsmul, smul_mul_assoc,
      mul_smul_comm]
  have htriv : ∀ s, t.Coprime s → (actLat γ.1 Λ).TrivAt s := fun s hs =>
    ⟨t, hs, (GlobalTheory.GenusLatCompare.span_smul_le_iff _ _ _).2 (by
      rintro _ ⟨v, hv, rfl⟩
      exact h1 v hv), (GlobalTheory.GenusLatCompare.span_smul_le_iff _ _ _).2 h2⟩
  refine ⟨γ.1, ?_, htriv _ ht.coprime_mul_left_right, htriv _ ht.coprime_mul_right_right, fun v x hx => ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (GlobalTheory.UnRep.StdInhab.isUnE_one_iff _ _).1 hγ i j]
    rfl
  · obtain ⟨w, hw, e⟩ := key v v.2
    obtain ⟨w', hw', e'⟩ := hg3 v x (funext hx)
    have hME : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    set u : Fin n → E := (m : E)⁻¹ • (t • (γ.1 *ᵥ (v : Fin n → E) - fun j => (x j : E))) with hu
    have hmu : m • u = t • (γ.1 *ᵥ (v : Fin n → E) - fun j => (x j : E)) := by
      rw [hu, ← Nat.cast_smul_eq_nsmul E m, smul_smul, mul_inv_cancel₀ hME, one_smul]
    have e2 : fv (maximalRealSubfield E) u = t • w' + w := by
      refine lim_nsmul_cancel (maximalRealSubfield E) hm ?_
      rw [← cap_fv_nsmul, hmu, cap_fv_nsmul, fv_sub, smul_sub, e, e', smul_add, smul_add, smul_comm t m]
      abel
    have hu' : u ∈ stdLat E n := by
      rw [← hrat, e2]
      exact add_mem (nsmul_mem hw' _) hw
    obtain ⟨b, hb⟩ := inc_surjective ⟨_, hu'⟩
    refine ⟨t, ht.coprime_mul_right_right, fun j => ⟨b j, ?_⟩⟩
    have hb' : (b j : E) = u j := congrFun (congrArg Subtype.val hb) j
    have := congrFun hmu j
    simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul] at this
    rw [hb']
    exact this.symm

end GlobalTheory.RepTrivial
