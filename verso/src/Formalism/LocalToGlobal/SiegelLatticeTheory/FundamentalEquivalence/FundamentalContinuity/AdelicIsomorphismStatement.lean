import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge

noncomputable section

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat Af IntAf)

variable (I : Formalism.MainNotions.S.AutInst)

abbrev TT : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E

abbrev EAf : Type := I.E ⊗[I.F] Af I.F

def CInt (c : ℕ) : Set (EAf I) := {w | ∃ t ∈ IntAf I.F I.E, w = (c : EAf I) * t}

def KgS (g : ℕ) : Set I.Gf :=
  {x | (x : GL (Fin I.n) (EAf I)) ∈ Formalism.UG.stabGL I.Lf ∧
    ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : EAf I) • z}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ z : I.E, z ∈ Set.range (algebraMap I.F I.E)`. Introduce `z`. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 I.E) z`.

Take `⟨x, hx⟩` from `hcon _ (by exact RingHom.mem_range.mpr ⟨a, rfl⟩)`. Take `⟨y, hy⟩` from `hcon _ (by exact RingHom.mem_range.mpr ⟨b, rfl⟩)`. Conclude with `⟨x / y, by rw [map_div₀, hx, hy]⟩`. Establish `hw : ∀ w : I.E, ∃ c : I.F, c • (1 : I.E) = w` using `fun w => by`. Take `⟨c, hc⟩` from `hall w`.

Conclude with `⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩`. Establish `hle : Module.finrank I.F I.E ≤ 1` using `by first`. Consider the case `exact finrank_le_one (1 : I.E) hw`. Consider the case `exact Module.finrank_le_one (1 : I.E) hw`. Establish `h2` using `I.cm.deg2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_beta : ∃ β : I.E, β ∈ Formalism.UG.intOE I.E ∧ β ∉ Set.range (algebraMap I.F I.E) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ z : I.E, z ∈ Set.range (algebraMap I.F I.E) := by
    intro z
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) z
    obtain ⟨x, hx⟩ := hcon _ (by exact RingHom.mem_range.mpr ⟨a, rfl⟩)
    obtain ⟨y, hy⟩ := hcon _ (by exact RingHom.mem_range.mpr ⟨b, rfl⟩)
    exact ⟨x / y, by rw [map_div₀, hx, hy]⟩
  have hw : ∀ w : I.E, ∃ c : I.F, c • (1 : I.E) = w := fun w => by
    obtain ⟨c, hc⟩ := hall w
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  have hle : Module.finrank I.F I.E ≤ 1 := by
    first
      | exact finrank_le_one (1 : I.E) hw
      | exact Module.finrank_le_one (1 : I.E) hw
  have h2 := I.cm.deg2
  omega

def beta : I.E := (exists_beta I).choose

/- English proof (translation)
The claim follows from `(exists_beta I).choose_spec.1`.
-/
theorem beta_int : beta I ∈ Formalism.UG.intOE I.E := (exists_beta I).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_beta I).choose_spec.2`.
-/
theorem beta_notF : beta I ∉ Set.range (algebraMap I.F I.E) := (exists_beta I).choose_spec.2

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Use `⟨by simpa using h, rfl⟩` and prove the remaining obligations.

It suffices to derive a contradiction. Apply `beta_notF I` to reduce the goal to its premises. Establish `h2 : t • beta I = -(s • (1 : I.E))`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `h`.

Use `⟨-(s / t), ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`. Use `_ = t⁻¹ • (t • beta I) := by rw [h2]`.

Use `_ = beta I := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]`.
-/
theorem linIndep_one_beta : LinearIndependent I.F ![(1 : I.E), beta I] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  by_cases ht : t = 0
  · subst ht
    refine ⟨by simpa using h, rfl⟩
  · exfalso
    apply beta_notF I
    have h2 : t • beta I = -(s • (1 : I.E)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    refine ⟨-(s / t), ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    calc (-(s / t)) • (1 : I.E) = t⁻¹ • (-(s • (1 : I.E))) := by
          rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • beta I) := by rw [h2]
      _ = beta I := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

def bas : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_beta I) (by simp [I.cm.deg2])

/- English proof (translation)
Simplify using `[bas]`.
-/
theorem bas_zero : bas I 0 = 1 := by
  simp [bas]

/- English proof (translation)
Simplify using `[bas]`.
-/
theorem bas_one : bas I 1 = beta I := by
  simp [bas]

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ S`. Use `⟨y.natAbs * y.natAbs, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `Int.natAbs_pos.mpr hy0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc : ((y.natAbs * y.natAbs : ℕ) : I.E) = ((y * y : ℤ) : I.E)`.

Rewrite using `[← Int.cast_natCast (R := I.E), Int.natAbs_mul_self]`. Establish `hyI : IsIntegral ℤ (y : I.E)`. Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ I.E y))`. Establish `h2 : IsIntegral ℤ ((y : I.E) * (y • x))` using `hyI.mul (hy x hx)`. Establish `h3 : ((y * y : ℤ) : I.E) * x = (y : I.E) * (y • x)`.

Rewrite using `[zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, h3]`. Conclude with `⟨⟨_, h2⟩, rfl⟩`.
-/
theorem lat_denom (S : Finset I.E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ S, (d : I.E) * x ∈ Formalism.UG.intOE I.E := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ S
  refine ⟨y.natAbs * y.natAbs, ?_, fun x hx => ?_⟩
  · have h := Int.natAbs_pos.mpr hy0
    nlinarith
  · have hc : ((y.natAbs * y.natAbs : ℕ) : I.E) = ((y * y : ℤ) : I.E) := by
      rw [← Int.cast_natCast (R := I.E), Int.natAbs_mul_self]
    have hyI : IsIntegral ℤ (y : I.E) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ I.E y))
    have h2 : IsIntegral ℤ ((y : I.E) * (y • x)) := hyI.mul (hy x hx)
    have h3 : ((y * y : ℤ) : I.E) * x = (y : I.E) * (y • x) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [hc, h3]
    exact ⟨⟨_, h2⟩, rfl⟩

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `I.L.nsmul_mem hu d`.
-/
theorem lat_mem_smul_nat {d : ℕ} {u : Fin I.n → I.E} (hu : u ∈ I.L) : (d : I.E) • u ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact I.L.nsmul_mem hu d

/- English proof (translation)
Establish `hv : v ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E))`. Rewrite using `[I.L_span]`. Conclude with `Submodule.mem_top`. Take `⟨k, f, g, hfg⟩` from `Submodule.mem_span_set'.mp hv`. Take `⟨d, hd, hdi⟩` from `lat_denom I (Finset.univ.image f)`.

Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfg, Finset.smul_sum]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Take `⟨o, ho⟩` from `hdi (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))`. Rewrite using `[smul_smul, ← ho, algebraMap_smul]`.

Conclude with `I.L.smul_mem o (g i).2`.
-/
theorem lat_mult_mem (v : Fin I.n → I.E) : ∃ d : ℕ, 1 ≤ d ∧ (d : I.E) • v ∈ I.L := by
  classical
  have hv : v ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)) := by
    rw [I.L_span]
    exact Submodule.mem_top
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨d, hd, hdi⟩ := lat_denom I (Finset.univ.image f)
  refine ⟨d, hd, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  obtain ⟨o, ho⟩ := hdi (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  rw [smul_smul, ← ho, algebraMap_smul]
  exact I.L.smul_mem o (g i).2

/- English proof (translation)
Take `⟨s, hs⟩` from `I.L_fg`. Take `⟨d', hd', hd'i⟩` from `lat_denom I (s.biUnion fun g => Finset.univ.image g)`. Establish `hB : ∀ l ∈ I.L, ∀ i, (d' : I.E) * l i ∈ Formalism.UG.intOE I.E`. Introduce `l hl`. Rewrite `hl` using `[← hs]`.

Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `i`. Conclude with `hd'i (x i) (Finset.mem_biUnion.mpr ⟨x, Finset.mem_coe.mp hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)`. Consider the case `zero`.

Introduce `i`. Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Introduce `i`.

Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `add_mem (hx i) (hy i)`. Consider the case `smul a x _ hx`. Introduce `i`. Establish `h1 : (d' : I.E) * (a • x) i = algebraMap (𝓞 I.E) I.E a * ((d' : I.E) * x i)`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `mul_mem ⟨a, rfl⟩ (hx i)`. Use `choose dd hdd hmem using fun i => lat_mult_mem I (Pi.single i (1 : I.E))`.

Establish `hp : 1 ≤ ∏ i, dd i` using `Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => by have := hdd i; omega))`. Use `⟨(∏ i, dd i) * d', ?_, fun i => ?_, fun l hl i => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : (∏ j, dd j) * d' = dd i * ((∏ j ∈ Finset.univ.erase i, dd j) * d')`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : (Pi.single i (((∏ j, dd j) * d' : ℕ) : I.E) : Fin I.n → I.E) = (((∏ j ∈ Finset.univ.erase i, dd j) * d' : ℕ) : I.E) • ((dd i : I.E) • Pi.single i 1)`. Rewrite using `[hsplit]`. Use extensionality with `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.single_eq_of_ne h, Pi.smul_apply, smul_eq_mul, mul_zero]`.

Rewrite using `[e]`. Conclude with `lat_mem_smul_nat I (hmem i)`. Establish `h2 : (((∏ j, dd j) * d' : ℕ) : I.E) * l i = ((∏ j, dd j : ℕ) : I.E) * ((d' : I.E) * l i)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Conclude with `mul_mem ⟨((∏ j, dd j : ℕ) : 𝓞 I.E), by simp⟩ (hB l hl i)`.
-/
theorem lat_exists_m : ∃ m : ℕ, 1 ≤ m ∧ (∀ i, (Pi.single i (m : I.E) : Fin I.n → I.E) ∈ I.L) ∧
    ∀ l ∈ I.L, ∀ i, (m : I.E) * l i ∈ Formalism.UG.intOE I.E := by
  classical

  obtain ⟨s, hs⟩ := I.L_fg
  obtain ⟨d', hd', hd'i⟩ := lat_denom I (s.biUnion fun g => Finset.univ.image g)
  have hB : ∀ l ∈ I.L, ∀ i, (d' : I.E) * l i ∈ Formalism.UG.intOE I.E := by
    intro l hl
    rw [← hs] at hl
    induction hl using Submodule.span_induction with
    | mem x hx =>
      intro i
      exact hd'i (x i) (Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_coe.mp hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    | zero =>
      intro i
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro i
      rw [Pi.add_apply, mul_add]
      exact add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      have h1 : (d' : I.E) * (a • x) i = algebraMap (𝓞 I.E) I.E a * ((d' : I.E) * x i) := by
        rw [Pi.smul_apply, Algebra.smul_def]
        ring
      rw [h1]
      exact mul_mem ⟨a, rfl⟩ (hx i)

  choose dd hdd hmem using fun i => lat_mult_mem I (Pi.single i (1 : I.E))
  have hp : 1 ≤ ∏ i, dd i := Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    (fun i _ => by have := hdd i; omega))
  refine ⟨(∏ i, dd i) * d', ?_, fun i => ?_, fun l hl i => ?_⟩
  · calc 1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul hp hd'
  · have hsplit : (∏ j, dd j) * d' = dd i * ((∏ j ∈ Finset.univ.erase i, dd j) * d') := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      ring
    have e : (Pi.single i (((∏ j, dd j) * d' : ℕ) : I.E) : Fin I.n → I.E) =
        (((∏ j ∈ Finset.univ.erase i, dd j) * d' : ℕ) : I.E) • ((dd i : I.E) • Pi.single i 1) := by
      rw [hsplit]
      ext j
      by_cases h : j = i
      · subst h
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]
        push_cast
        ring
      · simp only [Pi.single_eq_of_ne h, Pi.smul_apply, smul_eq_mul, mul_zero]
    rw [e]
    exact lat_mem_smul_nat I (hmem i)
  · have h2 : (((∏ j, dd j) * d' : ℕ) : I.E) * l i = ((∏ j, dd j : ℕ) : I.E) * ((d' : I.E) * l i) := by
      push_cast
      ring
    rw [h2]
    exact mul_mem ⟨((∏ j, dd j : ℕ) : 𝓞 I.E), by simp⟩ (hB l hl i)

/- English proof (translation)
Conclude with `lat_exists_m I`.
-/
theorem exists_m : ∃ m : ℕ, 1 ≤ m ∧ (∀ i, (Pi.single i (m : I.E) : Fin I.n → I.E) ∈ I.L) ∧
    ∀ l ∈ I.L, ∀ i, (m : I.E) * l i ∈ Formalism.UG.intOE I.E := by
  exact lat_exists_m I

def mm : ℕ := (exists_m I).choose

/- English proof (translation)
The claim follows from `(exists_m I).choose_spec.1`.
-/
theorem mm_pos : 1 ≤ mm I := (exists_m I).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_m I).choose_spec.2.1 i`.
-/
theorem mm_single (i : Fin I.n) : (Pi.single i (mm I : I.E) : Fin I.n → I.E) ∈ I.L := (exists_m I).choose_spec.2.1 i

/- English proof (translation)
The claim follows from `(exists_m I).choose_spec.2.2 l hl i`.
-/
theorem mm_int (l : Fin I.n → I.E) (hl : l ∈ I.L) (i : Fin I.n) :
    (mm I : I.E) * l i ∈ Formalism.UG.intOE I.E := (exists_m I).choose_spec.2.2 l hl i

/- English proof (translation)
Establish `hk0 : (k : I.F) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Simplify using `using hk0.isUnit.map (algebraMap I.F (EAf I))`.
-/
theorem lat_isUnit (k : ℕ) (hk : 1 ≤ k) : IsUnit (k : EAf I) := by
  have hk0 : (k : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simpa using hk0.isUnit.map (algebraMap I.F (EAf I))

/- English proof (translation)
Apply `Subring.subset_closure` to reduce the goal to its premises. Conclude with `Or.inl ⟨⟨a, ha⟩, rfl⟩`.
-/
theorem lat_inclE_int (a : I.E) (ha : a ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  exact Or.inl ⟨⟨a, ha⟩, rfl⟩

/- English proof (translation)
Establish `h : (Pi.single i (mm I : EAf I) : Fin I.n → EAf I) = fun k => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((Pi.single i (mm I : I.E) : Fin I.n → I.E) k) := by`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hk]`. Rewrite using `[h]`. Conclude with `Submodule.subset_span ⟨⟨_, mm_single I i⟩, rfl⟩`.
-/
theorem lat_gen (i : Fin I.n) : (Pi.single i (mm I : EAf I) : Fin I.n → EAf I) ∈ I.Lf := by
  have h : (Pi.single i (mm I : EAf I) : Fin I.n → EAf I) =
      fun k => Formalism.UG.inclE (F := I.F) (Af I.F) ((Pi.single i (mm I : I.E) : Fin I.n → I.E) k) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.single_apply, hk]
  rw [h]
  exact Submodule.subset_span ⟨⟨_, mm_single I i⟩, rfl⟩

/- English proof (translation)
Establish `h : (mm I : EAf I) • v = ∑ j, (⟨v j, hv j⟩ : IntAf I.F I.E) • (Pi.single j (mm I : EAf I) : Fin I.n → EAf I)`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]`. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (lat_gen I j)`.
-/
theorem lat_smul_mem (v : Fin I.n → EAf I) (hv : ∀ i, v i ∈ IntAf I.F I.E) :
    (mm I : EAf I) • v ∈ I.Lf := by
  have h : (mm I : EAf I) • v =
      ∑ j, (⟨v j, hv j⟩ : IntAf I.F I.E) • (Pi.single j (mm I : EAf I) : Fin I.n → EAf I) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (lat_gen I j)

/- English proof (translation)
Introduce `i`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨l, hl⟩, rfl⟩` from `hx`. Establish `h` using `lat_inclE_int I _ (mm_int I l hl i)`.

Simplify `h` using `[map_mul, map_natCast]`. Consider the case `zero => simp`. Consider the case `add x1 y1 _ _ h1 h2`. Simplify `add_mem h1 h2` using `[mul_add]`. Consider the case `smul a x1 _ h1`.

Establish `h` using `mul_mem a.2 h1`. Simplify `h` using `[Subring.smul_def, mul_left_comm]`.
-/
theorem lat_int_of_mem (y : Fin I.n → EAf I) (hy : y ∈ I.Lf) :
    ∀ i, (mm I : EAf I) * y i ∈ IntAf I.F I.E := by
  intro i
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    have h := lat_inclE_int I _ (mm_int I l hl i)
    simpa [map_mul, map_natCast] using h
  | zero => simp
  | add x1 y1 _ _ h1 h2 =>
    simpa [mul_add] using add_mem h1 h2
  | smul a x1 _ h1 =>
    have h := mul_mem a.2 h1
    simpa [Subring.smul_def, mul_left_comm] using h

/- English proof (translation)
Establish `hM' : ∀ i j, ∃ t ∈ IntAf I.F I.E, M i j = ((g * mm I ^ 2 : ℕ) : EAf I) * t` using `hM`. Use `choose t ht hMt using hM'`. Use `⟨(mm I : EAf I) • fun i => ∑ j, t i j * ((mm I : EAf I) * y j), lat_smul_mem I _ (fun i => Subring.sum_mem _ fun j _ => mul_mem (ht i j) (lat_int_of_mem I y hy j)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hMt, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lat_mulVec (g : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (EAf I))
    (hM : ∀ i j, M i j ∈ CInt I (g * mm I ^ 2)) (y : Fin I.n → EAf I) (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, M *ᵥ y = (g : EAf I) • z := by
  have hM' : ∀ i j, ∃ t ∈ IntAf I.F I.E, M i j = ((g * mm I ^ 2 : ℕ) : EAf I) * t := hM
  choose t ht hMt using hM'
  refine ⟨(mm I : EAf I) • fun i => ∑ j, t i j * ((mm I : EAf I) * y j),
    lat_smul_mem I _ (fun i => Subring.sum_mem _ fun j _ => mul_mem (ht i j) (lat_int_of_mem I y hy j)), ?_⟩
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hMt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/- English proof (translation)
Take `⟨z, hz, he⟩` from `lat_mulVec I g M hM y hy`. Rewrite using `[he, Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hz g`.
-/
theorem lat_mulVec_mem (g : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (EAf I))
    (hM : ∀ i j, M i j ∈ CInt I (g * mm I ^ 2)) (y : Fin I.n → EAf I) (hy : y ∈ I.Lf) :
    M *ᵥ y ∈ I.Lf := by
  obtain ⟨z, hz, he⟩ := lat_mulVec I g M hM y hy
  rw [he, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hz g

/- English proof (translation)
Conclude with `Units.inv_mul (x : GL (Fin I.n) (EAf I))`.
-/
theorem lat_fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  exact Units.inv_mul (x : GL (Fin I.n) (EAf I))

/- English proof (translation)
Conclude with `Units.mul_inv (x : GL (Fin I.n) (EAf I))`.
-/
theorem lat_fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  exact Units.mul_inv (x : GL (Fin I.n) (EAf I))

/- English proof (translation)
Establish `h : I.fmat x *ᵥ y = (I.fmat x - 1) *ᵥ y + y`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[h]`. Conclude with `add_mem (lat_mulVec_mem I g _ h1 y hy) hy`.
-/
theorem lat_close_mem (g : ℕ) (x : I.Gf) (h1 : ∀ i j, (I.fmat x - 1) i j ∈ CInt I (g * mm I ^ 2))
    (y : Fin I.n → EAf I) (hy : y ∈ I.Lf) : I.fmat x *ᵥ y ∈ I.Lf := by
  have h : I.fmat x *ᵥ y = (I.fmat x - 1) *ᵥ y + y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [h]
  exact add_mem (lat_mulVec_mem I g _ h1 y hy) hy

/- English proof (translation)
Use `⟨?_, fun y hy => lat_mulVec I g _ h1 y hy⟩` and prove the remaining obligations. Use `show ∀ y : Fin I.n → EAf I, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf`. Introduce `y`. Use `⟨fun hy => lat_close_mem I g x h1 y hy, fun hy => ?_⟩` and prove the remaining obligations. Establish `h` using `lat_close_mem I g x⁻¹ h2 _ hy`.

Rewrite `h` using `[Matrix.mulVec_mulVec, lat_fmat_inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem kgS_of_close (g : ℕ) (hg : 1 ≤ g) (x : I.Gf)
    (h1 : ∀ i j, (I.fmat x - 1) i j ∈ CInt I (g * mm I ^ 2))
    (h2 : ∀ i j, (I.fmat x⁻¹ - 1) i j ∈ CInt I (g * mm I ^ 2)) : x ∈ KgS I g := by
  refine ⟨?_, fun y hy => lat_mulVec I g _ h1 y hy⟩
  show ∀ y : Fin I.n → EAf I, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf
  intro y
  refine ⟨fun hy => lat_close_mem I g x h1 y hy, fun hy => ?_⟩
  have h := lat_close_mem I g x⁻¹ h2 _ hy
  rwa [Matrix.mulVec_mulVec, lat_fmat_inv_mul, Matrix.one_mulVec] at h

/- English proof (translation)
Take `⟨hs, hk⟩` from `hx`. Establish `hxi : ∀ w : Fin I.n → EAf I, w ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ w ∈ I.Lf` using `inv_mem hs`. Use `⟨inv_mem hs, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hze⟩` from `hk y hy`. Use `⟨-(I.fmat x⁻¹ *ᵥ z), neg_mem ((hxi z).1 hz), ?_⟩` and prove the remaining obligations.

Establish `key : I.fmat x⁻¹ - 1 = -(I.fmat x⁻¹ * (I.fmat x - 1))`. Rewrite using `[mul_sub, lat_fmat_inv_mul, mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[key, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hze, Matrix.mulVec_smul, smul_neg]`.
-/
theorem lat_inv_mem (g : ℕ) (x : I.Gf) (hx : x ∈ KgS I g) : x⁻¹ ∈ KgS I g := by
  obtain ⟨hs, hk⟩ := hx
  have hxi : ∀ w : Fin I.n → EAf I, w ∈ I.Lf ↔ I.fmat x⁻¹ *ᵥ w ∈ I.Lf := inv_mem hs
  refine ⟨inv_mem hs, fun y hy => ?_⟩
  obtain ⟨z, hz, hze⟩ := hk y hy
  refine ⟨-(I.fmat x⁻¹ *ᵥ z), neg_mem ((hxi z).1 hz), ?_⟩
  have key : I.fmat x⁻¹ - 1 = -(I.fmat x⁻¹ * (I.fmat x - 1)) := by
    rw [mul_sub, lat_fmat_inv_mul, mul_one]
    abel
  rw [key, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hze, Matrix.mulVec_smul, smul_neg]

/- English proof (translation)
Introduce `i j`. Take `⟨z, hz, hze⟩` from `hx.2 _ (lat_gen I j)`. Establish `h : (I.fmat x - 1) i j * (mm I : EAf I) = ((c * mm I ^ 2 : ℕ) : EAf I) * z i`. Simplify `congrFun hze i` using `[Matrix.mulVec_single]`. Use `⟨(mm I : EAf I) * z i, lat_int_of_mem I z hz i, ?_⟩` and prove the remaining obligations.

Apply `(IsUnit.mul_left_inj (lat_isUnit I (mm I) (mm_pos I))).mp` to reduce the goal to its premises. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lat_col (c : ℕ) (x : I.Gf) (hx : x ∈ KgS I (c * mm I ^ 2)) :
    ∀ i j, (I.fmat x - 1) i j ∈ CInt I c := by
  intro i j
  obtain ⟨z, hz, hze⟩ := hx.2 _ (lat_gen I j)
  have h : (I.fmat x - 1) i j * (mm I : EAf I) = ((c * mm I ^ 2 : ℕ) : EAf I) * z i := by
    simpa [Matrix.mulVec_single] using congrFun hze i
  refine ⟨(mm I : EAf I) * z i, lat_int_of_mem I z hz i, ?_⟩
  apply (IsUnit.mul_left_inj (lat_isUnit I (mm I) (mm_pos I))).mp
  rw [h]
  push_cast
  ring

/- English proof (translation)
Introduce `i j` and use `⟨lat_col I c x hx i j, lat_col I c x⁻¹ (lat_inv_mem I _ x hx) i j⟩`.
-/
theorem close_of_kgS (c : ℕ) (hc : 1 ≤ c) (x : I.Gf) (hx : x ∈ KgS I (c * mm I ^ 2)) :
    ∀ i j, (I.fmat x - 1) i j ∈ CInt I c ∧ (I.fmat x⁻¹ - 1) i j ∈ CInt I c := fun i j => ⟨lat_col I c x hx i j, lat_col I c x⁻¹ (lat_inv_mem I _ x hx) i j⟩

def alg_B : Module.Basis (Fin 2) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I) :=
  Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (bas I)

def alg_Bf : Module.Basis (Fin 2) (Af I.F) (Af I.F ⊗[I.F] I.E) :=
  Algebra.TensorProduct.basis (Af I.F) (bas I)

/- English proof (translation)
Use `conv_lhs => rw [← (alg_B I).sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[alg_B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem alg_y_eq (y : TT I) : y = ∑ i, (alg_B I).repr y i ⊗ₜ[I.F] bas I i := by
  conv_lhs => rw [← (alg_B I).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [alg_B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem alg_evV_apply (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) :
    evV I v a = InfinitePlace.Completion.extensionEmbedding v (a.1 v) := rfl

/- English proof (translation)
Rewrite using `[alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (I.cm.totReal.isReal v)]`. Conclude with `Complex.ofReal_im _`.
-/
theorem alg_evV_real (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) :
    (evV I v a).im = 0 := by
  rw [alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply
    (I.cm.totReal.isReal v)]
  exact Complex.ofReal_im _

/- English proof (translation)
Introduce `h0`. Establish `hv : v.IsReal` using `I.cm.totReal.isReal v`. Establish `hemb : ∀ c : I.F, (v.embedding c).im = 0` using `fun c => by`. Establish `h` using `NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hv)`. Establish `h2` using `RingHom.congr_fun h c`.

Rewrite `h2` using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.mp h2`. Establish `hall : ∀ e : I.E, (I.φ v e).im = 0`. Introduce `e`. Rewrite using `[← (bas I).sum_repr e, Fin.sum_univ_two, bas_zero, bas_one]`.

Simplify using `[Algebra.smul_def, I.φ_over, Complex.mul_im, hemb, h0]`. Establish `hreal : NumberField.ComplexEmbedding.IsReal (I.φ v)` using `NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun e => by`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.mpr (hall e))`. Establish `hw : (NumberField.InfinitePlace.mk (I.φ v)).IsReal` using `⟨I.φ v, hreal, rfl⟩`.

Use `haveI := I.cm.cmUnram.1`. Conclude with `NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex _) hw`.
-/
theorem alg_im_ne (v : InfinitePlace I.F) : (I.φ v (beta I)).im ≠ 0 := by
  intro h0
  have hv : v.IsReal := I.cm.totReal.isReal v
  have hemb : ∀ c : I.F, (v.embedding c).im = 0 := fun c => by
    have h := NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hv)
    have h2 := RingHom.congr_fun h c
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    exact Complex.conj_eq_iff_im.mp h2

  have hall : ∀ e : I.E, (I.φ v e).im = 0 := by
    intro e
    rw [← (bas I).sum_repr e, Fin.sum_univ_two, bas_zero, bas_one]
    simp [Algebra.smul_def, I.φ_over, Complex.mul_im, hemb, h0]
  have hreal : NumberField.ComplexEmbedding.IsReal (I.φ v) :=
    NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun e => by
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (hall e))
  have hw : (NumberField.InfinitePlace.mk (I.φ v)).IsReal := ⟨I.φ v, hreal, rfl⟩
  haveI := I.cm.cmUnram.1
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (NumberField.IsTotallyComplex.isComplex _) hw

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [thetaV]`.
-/
private theorem thetaV_tmul_lemma_2 (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (b : I.E) :
    thetaV I v (a ⊗ₜ[I.F] b) = evV I v a * I.φ v b := by
  first
    | rfl
    | simp [thetaV]

/- English proof (translation)
Use `conv_lhs => rw [alg_y_eq I y]`. Rewrite using `[map_sum, Fin.sum_univ_two, thetaV_tmul_lemma_2, thetaV_tmul_lemma_2, bas_zero, bas_one, map_one, mul_one]`.
-/
theorem alg_theta (v : InfinitePlace I.F) (y : TT I) :
    thetaV I v y = evV I v ((alg_B I).repr y 0) + evV I v ((alg_B I).repr y 1) * I.φ v (beta I) := by
  conv_lhs => rw [alg_y_eq I y]
  rw [map_sum, Fin.sum_univ_two, thetaV_tmul_lemma_2, thetaV_tmul_lemma_2, bas_zero, bas_one, map_one, mul_one]

/- English proof (translation)
Simplify using `only [tauF, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Apply the tactic sequence `try rfl`.
-/
private theorem tauF_tmul_lemma (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (b : I.E) :
    tauF I (a ⊗ₜ[I.F] b) = b ⊗ₜ[I.F] a.2 := by
  simp only [tauF, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  try rfl

/- English proof (translation)
Use `conv_lhs => rw [alg_y_eq I y]`. Rewrite using `[map_sum, Fin.sum_univ_two, tauF_tmul_lemma, tauF_tmul_lemma, bas_zero, bas_one]`.
-/
theorem alg_tau (y : TT I) :
    tauF I y = (1 : I.E) ⊗ₜ[I.F] ((alg_B I).repr y 0).2 + beta I ⊗ₜ[I.F] ((alg_B I).repr y 1).2 := by
  conv_lhs => rw [alg_y_eq I y]
  rw [map_sum, Fin.sum_univ_two, tauF_tmul_lemma, tauF_tmul_lemma, bas_zero, bas_one]

/- English proof (translation)
Simplify using `[alg_Bf, Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', bas_zero, bas_one]`.
-/
theorem alg_comm_eq (c : Fin 2 → Af I.F) :
    Algebra.TensorProduct.comm I.F I.E (Af I.F)
      ((1 : I.E) ⊗ₜ[I.F] c 0 + beta I ⊗ₜ[I.F] c 1) = ∑ i, c i • alg_Bf I i := by
  simp [alg_Bf, Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', bas_zero, bas_one]

/- English proof (translation)
Establish `h2 : ∑ i, c i • alg_Bf I i = 0` using `by rw [← alg_comm_eq I c, h, map_zero]`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp (alg_Bf I).linearIndependent c h2 i`.
-/
theorem alg_fin_inj (c : Fin 2 → Af I.F)
    (h : (1 : I.E) ⊗ₜ[I.F] c 0 + beta I ⊗ₜ[I.F] c 1 = 0) : c = 0 := by
  have h2 : ∑ i, c i • alg_Bf I i = 0 := by rw [← alg_comm_eq I c, h, map_zero]
  funext i
  exact Fintype.linearIndependent_iff.mp (alg_Bf I).linearIndependent c h2 i

/- English proof (translation)
Use `⟨fun i => (alg_Bf I).repr (Algebra.TensorProduct.comm I.F I.E (Af I.F) w) i, ?_⟩` and prove the remaining obligations. Apply `(Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective` to reduce the goal to its premises. Rewrite using `[alg_comm_eq]`. Conclude with `(alg_Bf I).sum_repr _`.
-/
theorem alg_fin_surj (w : EAf I) : ∃ c : Fin 2 → Af I.F,
    (1 : I.E) ⊗ₜ[I.F] c 0 + beta I ⊗ₜ[I.F] c 1 = w := by
  refine ⟨fun i => (alg_Bf I).repr (Algebra.TensorProduct.comm I.F I.E (Af I.F) w) i, ?_⟩
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  rw [alg_comm_eq]
  exact (alg_Bf I).sum_repr _

/- English proof (translation)
Establish `ha` using `alg_evV_real I v a`. Establish `hb` using `alg_evV_real I v b`. Establish `hβ` using `alg_im_ne I v`. Establish `him` using `congrArg Complex.im h`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.zero_im, ha, hb, zero_mul, add_zero, zero_add] at him`.

Establish `hbre : (evV I v b).re = 0`. Break down `mul_eq_zero.mp him with h0 | h0` into its components or cases. Conclude with `h0`. Conclude with `absurd h0 hβ`. Establish `hb0 : evV I v b = 0` using `Complex.ext hbre hb`.

Establish `ha0 : evV I v a = 0`. Rewrite `h` using `[hb0, zero_mul, add_zero]`. Conclude with `h`. Rewrite `ha0`, `hb0` using `[alg_evV_apply]`. Conclude with `⟨(map_eq_zero_iff _ (RingHom.injective _)).mp ha0, (map_eq_zero_iff _ (RingHom.injective _)).mp hb0⟩`.
-/
theorem alg_inf_inj (v : InfinitePlace I.F) (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)
    (h : evV I v a + evV I v b * I.φ v (beta I) = 0) : a.1 v = 0 ∧ b.1 v = 0 := by
  have ha := alg_evV_real I v a
  have hb := alg_evV_real I v b
  have hβ := alg_im_ne I v
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.zero_im, ha, hb, zero_mul, add_zero, zero_add] at him
  have hbre : (evV I v b).re = 0 := by
    rcases mul_eq_zero.mp him with h0 | h0
    · exact h0
    · exact absurd h0 hβ
  have hb0 : evV I v b = 0 := Complex.ext hbre hb
  have ha0 : evV I v a = 0 := by
    rw [hb0, zero_mul, add_zero] at h
    exact h
  rw [alg_evV_apply] at ha0 hb0
  exact ⟨(map_eq_zero_iff _ (RingHom.injective _)).mp ha0, (map_eq_zero_iff _ (RingHom.injective _)).mp hb0⟩

/- English proof (translation)
Rewrite `h2` using `[alg_tau]`. Establish `hfin` using `alg_fin_inj I (fun i => ((alg_B I).repr y i).2) h2`. Establish `hc : ∀ i, (alg_B I).repr y i = 0`. Introduce `i`. Establish `h2i` using `congrFun hfin i`.

Use `Prod.ext ?_ h2i` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Establish `hv` using `alg_inf_inj I v ((alg_B I).repr y 0) ((alg_B I).repr y 1) (by rw [← alg_theta]; exact h1 v)`. Use `fin_cases i`. Conclude with `hv.1`.

Conclude with `hv.2`. Rewrite using `[alg_y_eq I y]`. Simplify using `[hc]`.
-/
theorem TT_ext (y : TT I) (h1 : ∀ v, thetaV I v y = 0) (h2 : tauF I y = 0) : y = 0 := by
  rw [alg_tau] at h2
  have hfin := alg_fin_inj I (fun i => ((alg_B I).repr y i).2) h2
  have hc : ∀ i, (alg_B I).repr y i = 0 := by
    intro i
    have h2i := congrFun hfin i
    refine Prod.ext ?_ h2i
    funext v
    have hv := alg_inf_inj I v ((alg_B I).repr y 0) ((alg_B I).repr y 1) (by rw [← alg_theta]; exact h1 v)
    fin_cases i
    · exact hv.1
    · exact hv.2
  rw [alg_y_eq I y]
  simp [hc]

/- English proof (translation)
Take `⟨c, hc⟩` from `alg_fin_surj I w`. Establish `hv : ∀ v : InfinitePlace I.F, v.IsReal` using `fun v => I.cm.totReal.isReal v`. Establish `he : ∀ v : InfinitePlace I.F, Function.Surjective (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal (hv v))` using `fun v => NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (hv v)`. Set `yr : InfinitePlace I.F → ℝ` to `fun v => (z v).im / (I.φ v (beta I)).im`. Set `xr : InfinitePlace I.F → ℝ` to `fun v => (z v).re - yr v * (I.φ v (beta I)).re`.

Set `xa : InfiniteAdeleRing I.F` to `fun v => Function.surjInv (he v) (xr v)`. Set `ya : InfiniteAdeleRing I.F` to `fun v => Function.surjInv (he v) (yr v)`. Set `A : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F` to `(xa, c 0)`. Set `B : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F` to `(ya, c 1)`. Use `⟨A ⊗ₜ[I.F] (1 : I.E) + B ⊗ₜ[I.F] beta I, fun v => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, thetaV_tmul_lemma_2, thetaV_tmul_lemma_2, map_one, mul_one]`. Establish `hA : evV I v A = (xr v : ℂ)`. Rewrite using `[alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v)]`. Conclude with `congrArg _ (Function.surjInv_eq (he v) (xr v))`. Establish `hB : evV I v B = (yr v : ℂ)`.

Rewrite using `[alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v)]`. Conclude with `congrArg _ (Function.surjInv_eq (he v) (yr v))`. Rewrite using `[hA, hB]`. Establish `hb` using `alg_im_ne I v`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, xr]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, zero_add, yr]`. Conclude with `div_mul_cancel₀ _ hb`. Rewrite using `[map_add, tauF_tmul_lemma, tauF_tmul_lemma]`.

Conclude with `hc`.
-/
theorem TT_surj (z : InfinitePlace I.F → ℂ) (w : EAf I) :
    ∃ y : TT I, (∀ v, thetaV I v y = z v) ∧ tauF I y = w := by
  obtain ⟨c, hc⟩ := alg_fin_surj I w
  have hv : ∀ v : InfinitePlace I.F, v.IsReal := fun v => I.cm.totReal.isReal v
  have he : ∀ v : InfinitePlace I.F,
      Function.Surjective (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal (hv v)) :=
    fun v => NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (hv v)

  let yr : InfinitePlace I.F → ℝ := fun v => (z v).im / (I.φ v (beta I)).im
  let xr : InfinitePlace I.F → ℝ := fun v => (z v).re - yr v * (I.φ v (beta I)).re
  let xa : InfiniteAdeleRing I.F := fun v => Function.surjInv (he v) (xr v)
  let ya : InfiniteAdeleRing I.F := fun v => Function.surjInv (he v) (yr v)
  let A : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F := (xa, c 0)
  let B : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F := (ya, c 1)
  refine ⟨A ⊗ₜ[I.F] (1 : I.E) + B ⊗ₜ[I.F] beta I, fun v => ?_, ?_⟩
  · rw [map_add, thetaV_tmul_lemma_2, thetaV_tmul_lemma_2, map_one, mul_one]
    have hA : evV I v A = (xr v : ℂ) := by
      rw [alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v)]
      exact congrArg _ (Function.surjInv_eq (he v) (xr v))
    have hB : evV I v B = (yr v : ℂ) := by
      rw [alg_evV_apply, ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v)]
      exact congrArg _ (Function.surjInv_eq (he v) (yr v))
    rw [hA, hB]
    have hb := alg_im_ne I v
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, xr]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        zero_add, yr]
      exact div_mul_cancel₀ _ hb
  · rw [map_add, tauF_tmul_lemma, tauF_tmul_lemma]
    exact hc

section AfFacts

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))`.
-/
theorem top_isOpen_intAd : IsOpen (Formalism.UG.intAd F : Set (Af F)) :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))

/- English proof (translation)
Use `first`. Consider the case `(have h : (N : v.adicCompletion F) = ((N : 𝓞 F) : v.adicCompletion F) := by simp`. Rewrite using `[h, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])`. Consider the case `(have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)`. Rewrite `h` using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`.

Simplify using `using h)`.
-/
theorem top_val_natCast (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  first
    | (have h : (N : v.adicCompletion F) = ((N : 𝓞 F) : v.adicCompletion F) := by simp
       rw [h, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
         IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap])
    | (have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
       rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at h
       simpa using h)

/- English proof (translation)
Rewrite `ht` using `[nhds_subtype_eq_comap, Filter.mem_comap]`. Take `⟨u, hu, hut⟩` from `ht`. Establish `hu' : u ∈ nhds (0 : v.adicCompletion F)` using `by simpa using hu`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.mp hu'`. Establish `hne` using `(γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero`.

Take `⟨a, ha⟩` from `WithZero.ne_zero_iff_exists.mp hne`. Establish `h1 : -((Multiplicative.toAdd a).natAbs : ℤ) ≤ Multiplicative.toAdd a`. Establish `h2` using `Int.le_natAbs (a := -Multiplicative.toAdd a)`. Rewrite `h2` using `[Int.natAbs_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨(Multiplicative.toAdd a).natAbs + 1, fun x hx => hut (hγ ?_)⟩` and prove the remaining obligations. Use `show Valued.v.restrict (x : v.adicCompletion F) < _`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, ← ha]`. Use `lt_of_le_of_lt hx ?_` and prove the remaining obligations. Establish `hK : -(((Multiplicative.toAdd a).natAbs + 1 : ℕ) : ℤ) < Multiplicative.toAdd a`.

Rewrite using `[Nat.cast_add, Nat.cast_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha' : (a : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd a)` using `rfl`. Rewrite using `[ha']`. Use `first`.

Consider the case `exact WithZero.exp_lt_exp.mpr hK`. Consider the case `exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr hK)`.
-/
theorem top_place_small (v : HeightOneSpectrum (𝓞 F)) (t : Set (v.adicCompletionIntegers F))
    (ht : t ∈ nhds 0) : ∃ K : ℕ, ∀ x : v.adicCompletionIntegers F,
      Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-(K : ℤ)) → x ∈ t := by
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at ht
  obtain ⟨u, hu, hut⟩ := ht
  have hu' : u ∈ nhds (0 : v.adicCompletion F) := by simpa using hu
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu'
  have hne := (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hne
  have h1 : -((Multiplicative.toAdd a).natAbs : ℤ) ≤ Multiplicative.toAdd a := by
    have h2 := Int.le_natAbs (a := -Multiplicative.toAdd a)
    rw [Int.natAbs_neg] at h2
    linarith
  refine ⟨(Multiplicative.toAdd a).natAbs + 1, fun x hx => hut (hγ ?_)⟩
  show Valued.v.restrict (x : v.adicCompletion F) < _
  rw [Valuation.restrict_lt_iff_lt_embedding, ← ha]
  refine lt_of_le_of_lt hx ?_
  have hK : -(((Multiplicative.toAdd a).natAbs + 1 : ℕ) : ℤ) < Multiplicative.toAdd a := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have ha' : (a : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd a) := rfl
  rw [ha']
  first
    | exact WithZero.exp_lt_exp.mpr hK
    | exact WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr hK)

/- English proof (translation)
Establish `hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : ValuationSubring (v.adicCompletion F)) : Set (v.adicCompletion F))` using `fun v => Valued.isOpen_valuationSubring _`. Establish `h0 : nhds (0 : Af F) = Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) (nhds 0)` using `RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (B := fun v => v.adicCompletionIntegers F) hopen`. Establish `hU' : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) ⁻¹' U ∈ nhds (0 : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F : Set (v.adicCompletion …`. Rewrite `hU` using `[h0]`. Conclude with `hU`.

Rewrite `hU'` using `[nhds_pi, Filter.mem_pi]`. Take `⟨S, hS, t, ht, hsub⟩` from `hU'`. Use `choose K hK using fun v => top_place_small F v (t v) (ht v)`. Take `⟨N, hN⟩ : ∃ N : ℕ, N = ∏ w ∈ hS.toFinset, Ideal.absNorm w.asIdeal ^ K w` from `⟨_, rfl⟩`. Use `⟨N, ?_, fun u hu => ?_⟩` and prove the remaining obligations.

Rewrite using `[hN, Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `w _`. Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h0`. Conclude with `w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)`.

Establish `hNmem : ∀ v : HeightOneSpectrum (𝓞 F), (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F` using `fun v => natCast_mem _ N`. Set `x : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F : Set (v.adicCompletion F))` to `fun v => ⟨(N : v.adicCompletion F) * u v, mul_mem (hNmem v) (hu v)⟩`. Establish `hx : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x = (N : Af F) * u`. Use extensionality with `v`. Use `first`.

Consider the case `rfl`. Consider the case `simp [x]`. Establish `hxin : x ∈ S.pi t`. Introduce `v hv`. Apply `hK v (x v)` to reduce the goal to its premises.

Establish `hvS : v ∈ hS.toFinset` using `hS.mem_toFinset.mpr hv`. Establish `hNv : Valued.v (N : v.adicCompletion F) ≤ WithZero.exp (-(K v : ℤ))`. Rewrite using `[top_val_natCast, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Establish `e : ((N : ℕ) : 𝓞 F) = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ^ (K v) * ((∏ w ∈ hS.toFinset.erase v, Ideal.absNorm w.asIdeal ^ K w : ℕ) : 𝓞 F)`. Rewrite using `[hN, ← Finset.mul_prod_erase _ _ hvS]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.absNorm_mem _) _)`. Establish `huv : Valued.v (u v) ≤ 1` using `(IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hu v)`.

Use `show Valued.v ((N : v.adicCompletion F) * u v) ≤ _`. Combine the equalities or inequalities in the displayed calculation. Establish `h : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x ∈ U` using `hsub hxin`. Rewrite `h` using `[hx]`. Conclude with `h`.
-/
theorem top_nhds_basis (U : Set (Af F)) (hU : U ∈ nhds (0 : Af F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ Formalism.UG.intAd F, (N : Af F) * u ∈ U := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : ValuationSubring (v.adicCompletion F)) : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  have h0 : nhds (0 : Af F) = Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) (nhds 0) :=
    RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (B := fun v => v.adicCompletionIntegers F) hopen
  have hU' : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) ⁻¹' U ∈
        nhds (0 : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    rw [h0] at hU
    exact hU
  rw [nhds_pi, Filter.mem_pi] at hU'
  obtain ⟨S, hS, t, ht, hsub⟩ := hU'

  choose K hK using fun v => top_place_small F v (t v) (ht v)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ∏ w ∈ hS.toFinset, Ideal.absNorm w.asIdeal ^ K w := ⟨_, rfl⟩
  refine ⟨N, ?_, fun u hu => ?_⟩
  · rw [hN, Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro w _
    apply pow_ne_zero
    intro h0
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have hNmem : ∀ v : HeightOneSpectrum (𝓞 F), (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
    fun v => natCast_mem _ N
  let x : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨(N : v.adicCompletion F) * u v, mul_mem (hNmem v) (hu v)⟩
  have hx : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x = (N : Af F) * u := by
    ext v
    first
      | rfl
      | simp [x]
  have hxin : x ∈ S.pi t := by
    intro v hv
    apply hK v (x v)
    have hvS : v ∈ hS.toFinset := hS.mem_toFinset.mpr hv
    have hNv : Valued.v (N : v.adicCompletion F) ≤ WithZero.exp (-(K v : ℤ)) := by
      rw [top_val_natCast, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
      have e : ((N : ℕ) : 𝓞 F) = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ^ (K v) *
          ((∏ w ∈ hS.toFinset.erase v, Ideal.absNorm w.asIdeal ^ K w : ℕ) : 𝓞 F) := by
        rw [hN, ← Finset.mul_prod_erase _ _ hvS]
        push_cast
        ring
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.absNorm_mem _) _)
    have huv : Valued.v (u v) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hu v)
    show Valued.v ((N : v.adicCompletion F) * u v) ≤ _
    calc Valued.v ((N : v.adicCompletion F) * u v) = Valued.v (N : v.adicCompletion F) * Valued.v (u v) :=
          Valuation.map_mul _ _ _
      _ ≤ WithZero.exp (-(K v : ℤ)) * 1 := mul_le_mul' hNv huv
      _ = _ := mul_one _
  have h : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x ∈ U := hsub hxin
  rw [hx] at h
  exact h

def top_cO (c : ℕ) : Set (Af F) := {a | ∃ u ∈ Formalism.UG.intAd F, a = (c : Af F) * u}

/- English proof (translation)
Establish `hu : IsUnit ((c : Af F))`. Establish `hc0 : (c : F) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Simplify using `using hc0.isUnit.map (algebraMap F (Af F))`. Take `⟨u, hu⟩` from `hu`. Establish `h : top_cO F c = (fun a => (↑u⁻¹ : Af F) * a) ⁻¹' (Formalism.UG.intAd F : Set (Af F))`.

Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩ show (↑u⁻¹ : Af F) * ((c : Af F) * t) ∈ Formalism.UG.intAd F`. Rewrite using `[← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `ht`.

Introduce `ha`. Use `⟨_, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[h]`. Conclude with `(top_isOpen_intAd F).preimage (continuous_const.mul continuous_id)`.
-/
theorem top_isOpen_cO (c : ℕ) (hc : 1 ≤ c) : IsOpen (top_cO F c) := by
  have hu : IsUnit ((c : Af F)) := by
    have hc0 : (c : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using hc0.isUnit.map (algebraMap F (Af F))
  obtain ⟨u, hu⟩ := hu
  have h : top_cO F c = (fun a => (↑u⁻¹ : Af F) * a) ⁻¹' (Formalism.UG.intAd F : Set (Af F)) := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      show (↑u⁻¹ : Af F) * ((c : Af F) * t) ∈ Formalism.UG.intAd F
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      exact ht
    · intro ha
      refine ⟨_, ha, ?_⟩
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h]
  exact (top_isOpen_intAd F).preimage (continuous_const.mul continuous_id)

end AfFacts

section Coords

variable (I : Formalism.MainNotions.S.AutInst)

def top_bT : Module.Basis (Fin 2) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I) :=
  Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (bas I)

def top_eq : TT I ≃ₗ[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F] (Fin 2 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) :=
  (top_bT I).equivFun

instance top_imt : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I) := ⟨rfl⟩

instance top_cadd : ContinuousAdd (TT I) := IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I)

instance top_tag : IsTopologicalAddGroup (TT I) := IsModuleTopology.topologicalAddGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I)

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (top_eq I).toLinearMap`.
-/
theorem top_cont_eq : Continuous (top_eq I) := IsModuleTopology.continuous_of_linearMap (top_eq I).toLinearMap

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (top_eq I).symm.toLinearMap`.
-/
theorem top_cont_symm : Continuous (top_eq I).symm := IsModuleTopology.continuous_of_linearMap (top_eq I).symm.toLinearMap

/- English proof (translation)
Use `conv_lhs => rw [← (top_bT I).sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[top_eq, Module.Basis.equivFun_apply, top_bT, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem top_expand (y : TT I) : y = ∑ i, (top_eq I y i) ⊗ₜ[I.F] bas I i := by
  conv_lhs => rw [← (top_bT I).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [top_eq, Module.Basis.equivFun_apply, top_bT, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Use `conv_lhs => rw [top_expand I y]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => thetaV_tmul_lemma_2 I v _ _`.
-/
theorem top_theta_formula (v : InfinitePlace I.F) (y : TT I) :
    thetaV I v y = ∑ i, evV I v (top_eq I y i) * I.φ v (bas I i) := by
  conv_lhs => rw [top_expand I y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => thetaV_tmul_lemma_2 I v _ _

/- English proof (translation)
Use `conv_lhs => rw [top_expand I y]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => tauF_tmul_lemma I _ _`.
-/
theorem top_tau_formula (y : TT I) : tauF I y = ∑ i, bas I i ⊗ₜ[I.F] (top_eq I y i).2 := by
  conv_lhs => rw [top_expand I y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => tauF_tmul_lemma I _ _

/- English proof (translation)
Establish `h : ⇑(evV I v) = fun a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F => InfinitePlace.Completion.extensionEmbedding v (a.1 v)` using `funext fun a => alg_evV_apply I v a`. Rewrite using `[h]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp ((continuous_apply v).comp continuous_fst)`.
-/
theorem top_cont_evV (v : InfinitePlace I.F) : Continuous (evV I v) := by
  have h : ⇑(evV I v) = fun a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F =>
      InfinitePlace.Completion.extensionEmbedding v (a.1 v) := funext fun a => alg_evV_apply I v a
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
    ((continuous_apply v).comp continuous_fst)

/- English proof (translation)
The claim follows from `(continuous_apply i).comp (top_cont_eq I)`.
-/
theorem top_cont_coord (i : Fin 2) : Continuous fun y : TT I => top_eq I y i := (continuous_apply i).comp (top_cont_eq I)

/- English proof (translation)
Establish `h : ⇑(thetaV I v) = fun y => ∑ i, evV I v (top_eq I y i) * I.φ v (bas I i)`. Use function extensionality and compare the values at `fun y => top_theta_formula I v y`. Rewrite using `[h]`. Conclude with `continuous_finset_sum _ fun i _ => ((top_cont_evV I v).comp (top_cont_coord I i)).mul continuous_const`.
-/
theorem continuous_thetaV (v : InfinitePlace I.F) : Continuous (thetaV I v) := by
  have h : ⇑(thetaV I v) = fun y => ∑ i, evV I v (top_eq I y i) * I.φ v (bas I i) :=
    funext fun y => top_theta_formula I v y
  rw [h]
  exact continuous_finset_sum _ fun i _ => ((top_cont_evV I v).comp (top_cont_coord I i)).mul continuous_const

/- English proof (translation)
Conclude with `(map_natCast (Algebra.TensorProduct.includeRight : Af I.F →ₐ[I.F] EAf I) c).symm`.
-/
theorem top_natCast_EAf (c : ℕ) : (c : EAf I) = (1 : I.E) ⊗ₜ[I.F] (c : Af I.F) := by
  exact (map_natCast (Algebra.TensorProduct.includeRight : Af I.F →ₐ[I.F] EAf I) c).symm

/- English proof (translation)
Use `fin_cases i`. Simplify using `[bas_zero I]`. Simplify `beta_int I` using `[bas_one I]`.
-/
theorem top_bas_int (i : Fin 2) : bas I i ∈ Formalism.UG.intOE I.E := by
  fin_cases i
  · simp [bas_zero I]
  · simpa [bas_one I] using beta_int I

/- English proof (translation)
Establish `h : x ⊗ₜ[I.F] u = (x ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] u)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[h]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩))`.
-/
theorem top_tmul_mem_int (x : I.E) (hx : x ∈ Formalism.UG.intOE I.E) (u : Af I.F) (hu : u ∈ Formalism.UG.intAd I.F) :
    x ⊗ₜ[I.F] u ∈ IntAf I.F I.E := by
  have h : x ⊗ₜ[I.F] u = (x ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] u) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩))

def top_CIntSub (c : ℕ) : AddSubgroup (EAf I) where
  carrier := CInt I c
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, add_mem hs ht, by rw [mul_add]⟩
  neg_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨-s, neg_mem hs, by rw [mul_neg]⟩

/- English proof (translation)
Set `H : AddSubgroup (TT I)` to `(top_CIntSub I c).comap (tauF I).toAddMonoidHom`. Establish `hO : IsOpen {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => (top_isOpen_cO I.F c hc).preimage (continuous_snd.comp (top_cont_coord I i))`. Establish `hsub : {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c} ⊆ (H : Set (TT I))`.

Introduce `y hy`. Use `choose u hu hyu using hy`. Use `show tauF I y ∈ CInt I c`. Use `⟨∑ i, bas I i ⊗ₜ[I.F] u i, sum_mem fun i _ => top_tmul_mem_int I _ (top_bas_int I i) _ (hu i), ?_⟩` and prove the remaining obligations. Rewrite using `[top_tau_formula, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hyu i, top_natCast_EAf, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `h0 : (0 : TT I) ∈ {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c}` using `fun i => ⟨0, zero_mem _, by rw [map_zero, mul_zero]; rfl⟩`. Conclude with `AddSubgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds h0) hsub)`.
-/
theorem isOpen_tauCInt (c : ℕ) (hc : 1 ≤ c) : IsOpen {y : TT I | tauF I y ∈ CInt I c} := by

  let H : AddSubgroup (TT I) := (top_CIntSub I c).comap (tauF I).toAddMonoidHom
  have hO : IsOpen {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (top_isOpen_cO I.F c hc).preimage (continuous_snd.comp (top_cont_coord I i))
  have hsub : {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c} ⊆ (H : Set (TT I)) := by
    intro y hy
    choose u hu hyu using hy
    show tauF I y ∈ CInt I c
    refine ⟨∑ i, bas I i ⊗ₜ[I.F] u i, sum_mem fun i _ => top_tmul_mem_int I _ (top_bas_int I i) _ (hu i), ?_⟩
    rw [top_tau_formula, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyu i, top_natCast_EAf, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h0 : (0 : TT I) ∈ {y : TT I | ∀ i, (top_eq I y i).2 ∈ top_cO I.F c} := fun i =>
    ⟨0, zero_mem _, by rw [map_zero, mul_zero]; rfl⟩
  exact AddSubgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds h0) hsub)

end Coords

section Small

variable (I : Formalism.MainNotions.S.AutInst)

def top_kappa (i : Fin 2) : EAf I →ₗ[I.F] Af I.F :=
  TensorProduct.lift ((LinearMap.lsmul I.F (Af I.F)).comp ((bas I).coord i))

/- English proof (translation)
Rewrite using `[top_kappa, TensorProduct.lift.tmul]`. Both sides reduce to the same expression.
-/
theorem top_kappa_tmul (i : Fin 2) (x : I.E) (a : Af I.F) :
    top_kappa I i (x ⊗ₜ[I.F] a) = (bas I).coord i x • a := by
  rw [top_kappa, TensorProduct.lift.tmul]
  rfl

/- English proof (translation)
Rewrite using `[top_kappa_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem top_kappa_bas (i j : Fin 2) (a : Af I.F) :
    top_kappa I i (bas I j ⊗ₜ[I.F] a) = if j = i then a else 0 := by
  rw [top_kappa_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[top_tau_formula, map_sum]`. Repeatedly rewrite using `[top_kappa_bas]`. Simplify using the standard rewrite rules.
-/
theorem top_kappa_tau (i : Fin 2) (y : TT I) : top_kappa I i (tauF I y) = (top_eq I y i).2 := by
  rw [top_tau_formula, map_sum]
  simp_rw [top_kappa_bas]
  simp

/- English proof (translation)
Rewrite using `[← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]`.
-/
theorem top_kappa_natMul (i : Fin 2) (c : ℕ) (t : EAf I) :
    top_kappa I i ((c : EAf I) * t) = (c : Af I.F) * top_kappa I i t := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

/- English proof (translation)
Use `fun v => ?_` and prove the remaining obligations. Use `show (algebraMap I.F (Af I.F) x) v ∈ v.adicCompletionIntegers I.F`. Take `⟨o, rfl⟩ : ∃ o : 𝓞 I.F, algebraMap (𝓞 I.F) I.F o = x` from `⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[IsDedekindDomain.FiniteAdeleRing.algebraMap_apply, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_le_one v o`.
-/
theorem top_int_algebraMap (x : I.F) (hx : IsIntegral ℤ x) :
    algebraMap I.F (Af I.F) x ∈ Formalism.UG.intAd I.F := by
  refine fun v => ?_
  show (algebraMap I.F (Af I.F) x) v ∈ v.adicCompletionIntegers I.F
  obtain ⟨o, rfl⟩ : ∃ o : 𝓞 I.F, algebraMap (𝓞 I.F) I.F o = x := ⟨⟨x, hx⟩, rfl⟩
  rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v o

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.biUnion fun k => Finset.univ.image fun i => (bas I).coord i (NumberField.RingOfIntegers.basis I.E k : I.E))`. Establish `key : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ (((y.natAbs * y.natAbs : ℕ) : I.F) * c)`. Introduce `c hc`. Establish `hc' : ((y.natAbs * y.natAbs : ℕ) : I.F) = ((y * y : ℤ) : I.F)`. Rewrite using `[← Int.cast_natCast (R := I.F), Int.natAbs_mul_self]`.

Establish `hyI : IsIntegral ℤ (y : I.F)`. Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ I.F y))`. Establish `h3 : ((y * y : ℤ) : I.F) * c = (y : I.F) * (y • c)`. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc', h3]`. Conclude with `hyI.mul hc`. Use `⟨y.natAbs * y.natAbs, ?_, fun o ho i => ?_⟩` and prove the remaining obligations. Establish `h` using `Int.natAbs_pos.mpr hy0`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨o', rfl⟩` from `ho`. Rewrite using `[← (NumberField.RingOfIntegers.basis I.E).sum_repr o', map_sum, map_sum, Finset.mul_sum]`. Use `IsIntegral.sum _ (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, mul_smul_comm]`.

Use `IsIntegral.smul _ (key _ (hy _ ?_))` and prove the remaining obligations. Conclude with `Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩`.
-/
theorem top_coord_den : ∃ D : ℕ, 1 ≤ D ∧ ∀ o ∈ Formalism.UG.intOE I.E, ∀ i : Fin 2,
    IsIntegral ℤ ((D : I.F) * (bas I).coord i o) := by
  classical

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.biUnion fun k =>
    Finset.univ.image fun i => (bas I).coord i (NumberField.RingOfIntegers.basis I.E k : I.E))
  have key : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ (((y.natAbs * y.natAbs : ℕ) : I.F) * c) := by
    intro c hc
    have hc' : ((y.natAbs * y.natAbs : ℕ) : I.F) = ((y * y : ℤ) : I.F) := by
      rw [← Int.cast_natCast (R := I.F), Int.natAbs_mul_self]
    have hyI : IsIntegral ℤ (y : I.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ I.F y))
    have h3 : ((y * y : ℤ) : I.F) * c = (y : I.F) * (y • c) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [hc', h3]
    exact hyI.mul hc
  refine ⟨y.natAbs * y.natAbs, ?_, fun o ho i => ?_⟩
  · have h := Int.natAbs_pos.mpr hy0
    nlinarith
  obtain ⟨o', rfl⟩ := ho
  rw [← (NumberField.RingOfIntegers.basis I.E).sum_repr o', map_sum, map_sum, Finset.mul_sum]
  refine IsIntegral.sum _ (fun k _ => ?_)
  rw [map_zsmul, map_zsmul, mul_smul_comm]
  refine IsIntegral.smul _ (key _ (hy _ ?_))
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩

/- English proof (translation)
Establish `hpure : ∀ x ∈ Formalism.UG.intOE I.E, ∀ u ∈ Formalism.UG.intAd I.F, (D : Af I.F) * top_kappa I i (x ⊗ₜ[I.F] u) ∈ Formalism.UG.intAd I.F`. Introduce `x hx u hu`. Rewrite using `[top_kappa_tmul, Algebra.smul_def, ← mul_assoc]`. Establish `e : (D : Af I.F) * algebraMap I.F (Af I.F) ((bas I).coord i x) = algebraMap I.F (Af I.F) ((D : I.F) * (bas I).coord i x)`. Rewrite using `[map_mul, map_natCast]`.

Rewrite using `[e]`. Conclude with `mul_mem (top_int_algebraMap I _ (hD x hx i)) hu`. Establish `hmon : ∀ m ∈ Submonoid.closure (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪ Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))), ∃ x ∈ Formalism.UG.intOE I.E, ∃ u ∈ Formalism.UG.intAd I.F, m = x ⊗ₜ[I.F] u`. Introduce `m hm`. Proceed by induction on `hm using Submonoid.closure_induction with`.

Consider the case `mem m hm`. Break down `hm with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩` into its components or cases. Conclude with `⟨x, hx, 1, one_mem _, rfl⟩`. Conclude with `⟨1, one_mem _, y, hy, rfl⟩`. Consider the case `one => exact ⟨1, one_mem _, 1, one_mem _, rfl⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨x, hx, u, hu, rfl⟩` from `ha`. Take `⟨x', hx', u', hu', rfl⟩` from `hb`. Conclude with `⟨x * x', mul_mem hx hx', u * u', mul_mem hu hu', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩`. Unfold `Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht`.

Establish `ht'` using `Subring.mem_closure_iff.mp ht`. Use `clear ht`. Proceed by induction on `ht' using AddSubgroup.closure_induction with`. Consider the case `mem m hm`. Take `⟨x, hx, u, hu, rfl⟩` from `hmon m hm`.

Conclude with `hpure x hx u hu`. Consider the case `zero`. Rewrite using `[map_zero, mul_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`.

Rewrite using `[map_add, mul_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha`. Rewrite using `[map_neg, mul_neg]`. Conclude with `neg_mem ha`.
-/
theorem top_kappa_int (D : ℕ)
    (hD : ∀ o ∈ Formalism.UG.intOE I.E, ∀ i : Fin 2, IsIntegral ℤ ((D : I.F) * (bas I).coord i o))
    (t : EAf I) (ht : t ∈ IntAf I.F I.E) (i : Fin 2) :
    (D : Af I.F) * top_kappa I i t ∈ Formalism.UG.intAd I.F := by

  have hpure : ∀ x ∈ Formalism.UG.intOE I.E, ∀ u ∈ Formalism.UG.intAd I.F,
      (D : Af I.F) * top_kappa I i (x ⊗ₜ[I.F] u) ∈ Formalism.UG.intAd I.F := by
    intro x hx u hu
    rw [top_kappa_tmul, Algebra.smul_def, ← mul_assoc]
    have e : (D : Af I.F) * algebraMap I.F (Af I.F) ((bas I).coord i x) =
        algebraMap I.F (Af I.F) ((D : I.F) * (bas I).coord i x) := by
      rw [map_mul, map_natCast]
    rw [e]
    exact mul_mem (top_int_algebraMap I _ (hD x hx i)) hu

  have hmon : ∀ m ∈ Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
        Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))),
      ∃ x ∈ Formalism.UG.intOE I.E, ∃ u ∈ Formalism.UG.intAd I.F, m = x ⊗ₜ[I.F] u := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      rcases hm with ⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · exact ⟨x, hx, 1, one_mem _, rfl⟩
      · exact ⟨1, one_mem _, y, hy, rfl⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, rfl⟩
    | mul a b _ _ ha hb =>
      obtain ⟨x, hx, u, hu, rfl⟩ := ha
      obtain ⟨x', hx', u', hu', rfl⟩ := hb
      exact ⟨x * x', mul_mem hx hx', u * u', mul_mem hu hu', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  have ht' := Subring.mem_closure_iff.mp ht
  clear ht
  induction ht' using AddSubgroup.closure_induction with
  | mem m hm =>
    obtain ⟨x, hx, u, hu, rfl⟩ := hmon m hm
    exact hpure x hx u hu
  | zero =>
    rw [map_zero, mul_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, mul_add]
    exact add_mem ha hb
  | neg a _ ha =>
    rw [map_neg, mul_neg]
    exact neg_mem ha

end Small

section Final

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Rewrite using `[alg_evV_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _).symm`.
-/
theorem top_norm_evV (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) :
    ‖a.1 v‖ = ‖evV I v a‖ := by
  rw [alg_evV_apply]
  exact ((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _).symm

/- English proof (translation)
Use `set b := I.φ v (beta I) with hb`. Establish `hs : 0 < |b.im|` using `abs_pos.mpr (alg_im_ne I v)`. Establish `hθ : thetaV I v y = evV I v (top_eq I y 0) + evV I v (top_eq I y 1) * b`. Rewrite using `[top_theta_formula, Fin.sum_univ_two, bas_zero, bas_one, map_one, mul_one]`. Establish `hr0` using `alg_evV_real I v (top_eq I y 0)`.

Establish `hr1` using `alg_evV_real I v (top_eq I y 1)`. Establish `hn0` using `top_norm_evV I v (top_eq I y 0)`. Establish `hn1'` using `top_norm_evV I v (top_eq I y 1)`. Use `set e0 := evV I v (top_eq I y 0) with he0`. Use `set e1 := evV I v (top_eq I y 1) with he1`.

Use `set θ := thetaV I v y with hθdef`. Establish `him : θ.im = e1.re * b.im`. Rewrite using `[hθ]`. Simplify using `[Complex.add_im, Complex.mul_im, hr0, hr1]`. Establish `hn1 : ‖e1‖ = |e1.re|`.

Establish `he : e1 = (e1.re : ℂ)` using `Complex.ext (by simp) (by simp [hr1])`. Rewrite using `[he]`. Use `first`. Consider the case `simp [Complex.norm_real]`. Consider the case `simp`.

Establish `himle : |θ.im| ≤ ‖θ‖` using `by first`. Consider the case `exact Complex.abs_im_le_norm θ`. Consider the case `exact Complex.abs_im_le_abs θ`. Establish `h1 : ‖e1‖ * |b.im| ≤ ‖θ‖`. Rewrite using `[hn1, ← abs_mul, ← him]`.

Conclude with `himle`. Establish `h0 : ‖e0‖ ≤ ‖θ‖ + ‖e1‖ * ‖b‖`. Establish `he : e0 = θ - e1 * b` using `by rw [hθ]; ring`. Rewrite using `[he]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hX` using `norm_nonneg θ`. Establish `hB` using `norm_nonneg b`. Establish `hs' : |b.im| ≠ 0` using `hs.ne'`. Establish `hT : (1 + (1 + ‖b‖) / |b.im|) * ‖θ‖ * |b.im| = ‖θ‖ * |b.im| + (1 + ‖b‖) * ‖θ‖`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Establish `k1` using `mul_le_mul_of_nonneg_right h0 hs.le`. Establish `k2` using `mul_le_mul_of_nonneg_left h1 hB`. Establish `k3` using `mul_nonneg hX hs.le`. Establish `k4` using `mul_nonneg hB hX`.

Use `fin_cases i`. Use `show ‖(top_eq I y 0).1 v‖ ≤ _`. Rewrite using `[hn0]`. Use `le_of_mul_le_mul_right ?_ hs` and prove the remaining obligations. Rewrite using `[hT]`.

Use the polynomial consequences of the given equalities and inequalities. Use `show ‖(top_eq I y 1).1 v‖ ≤ _`. Rewrite using `[hn1']`. Use `le_of_mul_le_mul_right ?_ hs` and prove the remaining obligations. Rewrite using `[hT]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem top_real_bound (v : InfinitePlace I.F) (y : TT I) (i : Fin 2) :
    ‖(top_eq I y i).1 v‖ ≤
      (1 + (1 + ‖I.φ v (beta I)‖) / |(I.φ v (beta I)).im|) * ‖thetaV I v y‖ := by
  set b := I.φ v (beta I) with hb
  have hs : 0 < |b.im| := abs_pos.mpr (alg_im_ne I v)
  have hθ : thetaV I v y = evV I v (top_eq I y 0) + evV I v (top_eq I y 1) * b := by
    rw [top_theta_formula, Fin.sum_univ_two, bas_zero, bas_one, map_one, mul_one]
  have hr0 := alg_evV_real I v (top_eq I y 0)
  have hr1 := alg_evV_real I v (top_eq I y 1)
  have hn0 := top_norm_evV I v (top_eq I y 0)
  have hn1' := top_norm_evV I v (top_eq I y 1)
  set e0 := evV I v (top_eq I y 0) with he0
  set e1 := evV I v (top_eq I y 1) with he1
  set θ := thetaV I v y with hθdef
  have him : θ.im = e1.re * b.im := by
    rw [hθ]
    simp [Complex.add_im, Complex.mul_im, hr0, hr1]
  have hn1 : ‖e1‖ = |e1.re| := by
    have he : e1 = (e1.re : ℂ) := Complex.ext (by simp) (by simp [hr1])
    rw [he]
    first
      | simp [Complex.norm_real]
      | simp
  have himle : |θ.im| ≤ ‖θ‖ := by
    first
      | exact Complex.abs_im_le_norm θ
      | exact Complex.abs_im_le_abs θ
  have h1 : ‖e1‖ * |b.im| ≤ ‖θ‖ := by
    rw [hn1, ← abs_mul, ← him]
    exact himle
  have h0 : ‖e0‖ ≤ ‖θ‖ + ‖e1‖ * ‖b‖ := by
    have he : e0 = θ - e1 * b := by rw [hθ]; ring
    rw [he]
    calc ‖θ - e1 * b‖ ≤ ‖θ‖ + ‖e1 * b‖ := norm_sub_le _ _
      _ = ‖θ‖ + ‖e1‖ * ‖b‖ := by rw [norm_mul]
  have hX := norm_nonneg θ
  have hB := norm_nonneg b
  have hs' : |b.im| ≠ 0 := hs.ne'
  have hT : (1 + (1 + ‖b‖) / |b.im|) * ‖θ‖ * |b.im| = ‖θ‖ * |b.im| + (1 + ‖b‖) * ‖θ‖ := by
    field_simp
    try ring
  have k1 := mul_le_mul_of_nonneg_right h0 hs.le
  have k2 := mul_le_mul_of_nonneg_left h1 hB
  have k3 := mul_nonneg hX hs.le
  have k4 := mul_nonneg hB hX
  fin_cases i
  · show ‖(top_eq I y 0).1 v‖ ≤ _
    rw [hn0]
    refine le_of_mul_le_mul_right ?_ hs
    rw [hT]
    nlinarith
  · show ‖(top_eq I y 1).1 v‖ ≤ _
    rw [hn1']
    refine le_of_mul_le_mul_right ?_ hs
    rw [hT]
    nlinarith

/- English proof (translation)
Establish `hW' : (top_eq I).symm ⁻¹' W ∈ nhds (0 : Fin 2 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)` using `(top_cont_symm I).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hW)`. Rewrite `hW'` using `[nhds_pi, Filter.mem_pi]`. Take `⟨Iset, -, t, ht, hsub⟩` from `hW'`. Establish `hprod : ∀ i, ∃ a ∈ nhds (0 : InfiniteAdeleRing I.F), ∃ b ∈ nhds (0 : Af I.F), a ×ˢ b ⊆ t i`. Introduce `i`.

Set `T : Set (InfiniteAdeleRing I.F × Af I.F)` to `t i`. Establish `hti : T ∈ nhds ((0 : InfiniteAdeleRing I.F), (0 : Af I.F))` using `ht i`. Rewrite `hti` using `[nhds_prod_eq, Filter.mem_prod_iff]`. Take `⟨a, ha, b, hb, hab⟩` from `hti`. Conclude with `⟨a, ha, b, hb, hab⟩`.

Use `choose a ha b hb hab using hprod`. Establish `hball : ∀ i, ∃ ε > (0 : ℝ), Metric.ball (0 : (v : InfinitePlace I.F) → v.Completion) ε ⊆ a i` using `fun i => Metric.mem_nhds_iff.mp (show a i ∈ nhds (0 : (v : InfinitePlace I.F) → v.Completion) from ha i)`. Use `choose ε hε hεsub using hball`. Use `choose N hN1 hNsub using fun i => top_nhds_basis I.F (b i) (hb i)`. Take `⟨D, hD1, hD⟩` from `top_coord_den I`.

Set `C : InfinitePlace I.F → ℝ` to `fun v => 1 + (1 + ‖I.φ v (beta I)‖) / |(I.φ v (beta I)).im|`. Establish `hC1 : ∀ v, 1 ≤ C v` using `fun v => by`. Establish `: 0 ≤ (1 + ‖I.φ v (beta I)‖) / |(I.φ v (beta I)).im|` using `by positivity`. Simplify using `only [C]`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `M : ℝ` to `1 + ∑ v, C v`. Establish `hCM : ∀ v, C v ≤ M` using `fun v => by`. Use `Finset.single_le_sum (fun w _ => (zero_le_one.trans (hC1 w))) (Finset.mem_univ v)` as an intermediate fact. Simplify using `only [M]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM : 0 < M` using `lt_of_lt_of_le zero_lt_one ((hC1 (Classical.arbitrary _)).trans (hCM _))`. Set `ε0 : ℝ` to `min (ε 0) (ε 1)`. Establish `hε0 : 0 < ε0` using `lt_min (hε 0) (hε 1)`. Establish `hε0i : ∀ i, ε0 ≤ ε i` using `fun i => by fin_cases i`. Conclude with `min_le_left _ _`.

Conclude with `min_le_right _ _`. Use `⟨ε0 / M, div_pos hε0 hM, D * (N 0 * N 1), ?_, fun y hθ hτ => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Set `Q : Fin 2 → ℕ` to `fun i => if i = 0 then N 1 else N 0`. Establish `hQ : ∀ i, N 0 * N 1 = N i * Q i`.

Introduce `i`. Use `fin_cases i`. Simplify using `[Q]`. Simplify using `[Q, mul_comm]`. Establish `hmem : ∀ i, top_eq I y i ∈ t i`.

Introduce `i`. Apply `hab i` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Apply `hεsub i` to reduce the goal to its premises. Set `x : (v : InfinitePlace I.F) → v.Completion` to `(top_eq I y i).1`.

Use `show x ∈ Metric.ball 0 (ε i)`. Rewrite using `[Metric.mem_ball, dist_pi_lt_iff (hε i)]`. Introduce `v`. Rewrite using `[Pi.zero_apply, dist_zero_right]`. Establish `hb'` using `top_real_bound I v y i`.

Establish `hθv` using `hθ v`. Establish `h1 : C v * ‖thetaV I v y‖ < C v * (ε0 / M)` using `mul_lt_mul_of_pos_left hθv (lt_of_lt_of_le zero_lt_one (hC1 v))`. Establish `h2 : C v * (ε0 / M) ≤ M * (ε0 / M)` using `mul_le_mul_of_nonneg_right (hCM v) (div_pos hε0 hM).le`. Establish `h3 : M * (ε0 / M) = ε0` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨s, hs, hτs⟩` from `hτ`. Rewrite using `[← top_kappa_tau, hτs, top_kappa_natMul]`. Establish `hk` using `top_kappa_int I D hD s hs i`. Establish `e : ((D * (N 0 * N 1) : ℕ) : Af I.F) * top_kappa I i s = (N i : Af I.F) * ((Q i : Af I.F) * ((D : Af I.F) * top_kappa I i s))`. Rewrite using `[hQ i]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hNsub i _ (mul_mem (natCast_mem _ _) hk)`. Establish `hy : (top_eq I).symm (top_eq I y) ∈ W` using `hsub (fun i _ => hmem i)`.

Simplify using `using hy`.
-/
theorem tt_small (W : Set (TT I)) (hW : W ∈ nhds (0 : TT I)) :
    ∃ δ > (0 : ℝ), ∃ c : ℕ, 1 ≤ c ∧ ∀ y : TT I, (∀ v, ‖thetaV I v y‖ < δ) →
      tauF I y ∈ CInt I c → y ∈ W := by
  classical

  have hW' : (top_eq I).symm ⁻¹' W ∈ nhds (0 : Fin 2 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) :=
    (top_cont_symm I).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hW)
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨Iset, -, t, ht, hsub⟩ := hW'
  have hprod : ∀ i, ∃ a ∈ nhds (0 : InfiniteAdeleRing I.F), ∃ b ∈ nhds (0 : Af I.F), a ×ˢ b ⊆ t i := by
    intro i
    let T : Set (InfiniteAdeleRing I.F × Af I.F) := t i
    have hti : T ∈ nhds ((0 : InfiniteAdeleRing I.F), (0 : Af I.F)) := ht i
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hti
    obtain ⟨a, ha, b, hb, hab⟩ := hti
    exact ⟨a, ha, b, hb, hab⟩
  choose a ha b hb hab using hprod

  have hball : ∀ i, ∃ ε > (0 : ℝ), Metric.ball (0 : (v : InfinitePlace I.F) → v.Completion) ε ⊆ a i :=
    fun i => Metric.mem_nhds_iff.mp (show a i ∈ nhds (0 : (v : InfinitePlace I.F) → v.Completion) from ha i)
  choose ε hε hεsub using hball

  choose N hN1 hNsub using fun i => top_nhds_basis I.F (b i) (hb i)
  obtain ⟨D, hD1, hD⟩ := top_coord_den I
  let C : InfinitePlace I.F → ℝ := fun v => 1 + (1 + ‖I.φ v (beta I)‖) / |(I.φ v (beta I)).im|
  have hC1 : ∀ v, 1 ≤ C v := fun v => by
    have : 0 ≤ (1 + ‖I.φ v (beta I)‖) / |(I.φ v (beta I)).im| := by positivity
    simp only [C]
    linarith
  let M : ℝ := 1 + ∑ v, C v
  have hCM : ∀ v, C v ≤ M := fun v => by
    have := Finset.single_le_sum (fun w _ => (zero_le_one.trans (hC1 w))) (Finset.mem_univ v)
    simp only [M]
    linarith
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one ((hC1 (Classical.arbitrary _)).trans (hCM _))
  let ε0 : ℝ := min (ε 0) (ε 1)
  have hε0 : 0 < ε0 := lt_min (hε 0) (hε 1)
  have hε0i : ∀ i, ε0 ≤ ε i := fun i => by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  refine ⟨ε0 / M, div_pos hε0 hM, D * (N 0 * N 1), ?_, fun y hθ hτ => ?_⟩
  · calc 1 = 1 * (1 * 1) := rfl
      _ ≤ D * (N 0 * N 1) := Nat.mul_le_mul hD1 (Nat.mul_le_mul (hN1 0) (hN1 1))
  let Q : Fin 2 → ℕ := fun i => if i = 0 then N 1 else N 0
  have hQ : ∀ i, N 0 * N 1 = N i * Q i := by
    intro i
    fin_cases i
    · simp [Q]
    · simp [Q, mul_comm]
  have hmem : ∀ i, top_eq I y i ∈ t i := by
    intro i
    apply hab i
    constructor
    ·
      apply hεsub i
      let x : (v : InfinitePlace I.F) → v.Completion := (top_eq I y i).1
      show x ∈ Metric.ball 0 (ε i)
      rw [Metric.mem_ball, dist_pi_lt_iff (hε i)]
      intro v
      rw [Pi.zero_apply, dist_zero_right]
      have hb' := top_real_bound I v y i
      have hθv := hθ v
      have h1 : C v * ‖thetaV I v y‖ < C v * (ε0 / M) :=
        mul_lt_mul_of_pos_left hθv (lt_of_lt_of_le zero_lt_one (hC1 v))
      have h2 : C v * (ε0 / M) ≤ M * (ε0 / M) :=
        mul_le_mul_of_nonneg_right (hCM v) (div_pos hε0 hM).le
      have h3 : M * (ε0 / M) = ε0 := by field_simp
      calc ‖(top_eq I y i).1 v‖ ≤ C v * ‖thetaV I v y‖ := hb'
        _ < C v * (ε0 / M) := h1
        _ ≤ M * (ε0 / M) := h2
        _ = ε0 := h3
        _ ≤ ε i := hε0i i
    ·
      obtain ⟨s, hs, hτs⟩ := hτ
      rw [← top_kappa_tau, hτs, top_kappa_natMul]
      have hk := top_kappa_int I D hD s hs i
      have e : ((D * (N 0 * N 1) : ℕ) : Af I.F) * top_kappa I i s =
          (N i : Af I.F) * ((Q i : Af I.F) * ((D : Af I.F) * top_kappa I i s)) := by
        rw [hQ i]
        push_cast
        ring
      rw [e]
      exact hNsub i _ (mul_mem (natCast_mem _ _) hk)
  have hy : (top_eq I).symm (top_eq I y) ∈ W := hsub (fun i _ => hmem i)
  simpa using hy

end Final

variable (I : Formalism.MainNotions.S.AutInst)

instance isModTop_TT : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I) := ⟨rfl⟩

instance isTopRing_TT : IsTopologicalRing (TT I) :=
  IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I)

instance isTopGroup_HAd : IsTopologicalGroup (HAd I) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))

def matHom : HAd I →* GL (Fin I.n) (TT I) :=
  (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matHom_apply (h : HAd I) : ((matHom I h : GL (Fin I.n) (TT I)) : Matrix _ _ _) = hmat I h := rfl

/- English proof (translation)
The claim follows from `continuous_subtype_val`.
-/
theorem continuous_matHom : Continuous (matHom I) := continuous_subtype_val

def Pu (v : InfinitePlace I.F) : GL (Fin I.n) ℂ := (I.P_unit v).unit

def FmInf (v : InfinitePlace I.F) : HAd I →* Formalism.REAL.UJ (I.ε v) :=
  ((MulAut.conj (Pu I v)⁻¹).toMonoidHom.comp ((Formalism.UG.bc (thetaV I v)).comp (matHom I))).codRestrict
    (Formalism.REAL.UJ (I.ε v)) (fun h => by
      show Formalism.REAL.inUJ (I.ε v) _
      convert ofHAInf_mem I h v using 1
      simp [ofHAInf, Pu, Formalism.UG.bc, matHom_apply, Matrix.coe_units_inv])

/- English proof (translation)
Simplify using `[FmInf, Pu, Formalism.UG.bc, matHom_apply, Matrix.coe_units_inv, ofHAInf, MulAut.conj_apply, mul_assoc, Formalism.MainNotions.S.uMat]`.
-/
theorem FmInf_val (v : InfinitePlace I.F) (h : HAd I) : uMat (FmInf I v h) = ofHAInf I h v := by
  simp [FmInf, Pu, Formalism.UG.bc, matHom_apply, Matrix.coe_units_inv, ofHAInf, MulAut.conj_apply, mul_assoc,
    Formalism.MainNotions.S.uMat]

def FmF : HAd I →* I.Gf :=
  ((Formalism.UG.bc (tauF I)).comp (matHom I)).codRestrict (Formalism.UG.UPts I.cm.sig I.J (Af I.F))
    (fun h => ofHAFin_mem I h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem FmF_val (h : HAd I) : I.fmat (FmF I h) = ofHAFin I h := rfl

def Fm : HAd I →* I.GA := MonoidHom.prod (MonoidHom.pi (FmInf I)) (FmF I)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fm_fst (h : HAd I) (v : InfinitePlace I.F) : (Fm I h).1 v = FmInf I v h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fm_snd (h : HAd I) : (Fm I h).2 = FmF I h := rfl

/- English proof (translation)
Establish `h` using `(Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.one_mul]`.
-/
theorem conj_cancel (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    I.P v * ((I.P v)⁻¹ * M * I.P v) * (I.P v)⁻¹ = M := by
  have h := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ h, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `(Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]`.
-/
theorem conj_cancel' (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    (I.P v)⁻¹ * (I.P v * M * (I.P v)⁻¹) * I.P v = M := by
  have h := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_one_apply {R : Type} [Ring R] (f : TT I →+* R) (i j : Fin I.n) :
    f ((1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j) = (1 : Matrix (Fin I.n) (Fin I.n) R) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Establish `hij` using `TT_ext I (A i j - B i j) (fun v => by`. Establish `h` using `congrFun (congrFun (h1 v) i) j`. Simplify using `only [Matrix.map_apply] at h`. Rewrite using `[map_sub, h, sub_self])`.

Use the proof step `(by`. Establish `h` using `congrFun (congrFun h2 i) j`. Simplify using `only [Matrix.map_apply] at h`. Rewrite using `[map_sub, h, sub_self])`. Conclude with `sub_eq_zero.mp hij`.
-/
theorem mat_ext (A B : Matrix (Fin I.n) (Fin I.n) (TT I))
    (h1 : ∀ v, A.map (thetaV I v) = B.map (thetaV I v)) (h2 : A.map (tauF I) = B.map (tauF I)) :
    A = B := by
  ext i j
  have hij := TT_ext I (A i j - B i j)
    (fun v => by
      have h := congrFun (congrFun (h1 v) i) j
      simp only [Matrix.map_apply] at h
      rw [map_sub, h, sub_self])
    (by
      have h := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at h
      rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp hij

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a b`. Establish `h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] b) = a ⊗ₜ[I.F] I.cm.sig b`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`.

Establish `h2 : Formalism.UG.sigR I.cm.sig (Af I.F) (b ⊗ₜ[I.F] a.2) = I.cm.sig b ⊗ₜ[I.F] a.2`. Simplify using `only [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[h1, tauF_tmul_lemma, tauF_tmul_lemma, h2]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tauF_sigR (x : TT I) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      Formalism.UG.sigR I.cm.sig (Af I.F) (tauF I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] b) =
        a ⊗ₜ[I.F] I.cm.sig b := by
      simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have h2 : Formalism.UG.sigR I.cm.sig (Af I.F) (b ⊗ₜ[I.F] a.2) = I.cm.sig b ⊗ₜ[I.F] a.2 := by
      simp only [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [h1, tauF_tmul_lemma, tauF_tmul_lemma, h2]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `h hh`. Establish `hinf : ∀ v, FmInf I v h = 1` using `fun v => by`. Establish `h0` using `congrArg (fun x : I.GA => x.1 v) hh`. Simplify `h0` using `[Fm_fst]`.

Establish `hfin : FmF I h = 1`. Establish `h0` using `congrArg Prod.snd hh`. Simplify `h0` using `[Fm_snd]`. Establish `hm : hmat I h = 1`. Apply `mat_ext` to reduce the goal to its premises.

Introduce `v`. Establish `hP` using `(Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)`. Establish `h1` using `congrArg Formalism.MainNotions.S.uMat (hinf v)`. Rewrite `h1` using `[FmInf_val]`. Establish `h2 : (hmat I h).map (thetaV I v) = I.P v * ofHAInf I h v * (I.P v)⁻¹`.

Rewrite using `[ofHAInf, conj_cancel]`. Rewrite using `[h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using `[Formalism.MainNotions.S.uMat, Matrix.mul_nonsing_inv _ hP]`. Establish `h3 : (hmat I h).map (tauF I) = I.fmat (FmF I h)` using `(FmF_val I h).symm`. Rewrite using `[h3, hfin, Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using `[Formalism.MainNotions.S.AutInst.fmat]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hm`.
-/
theorem Fm_injective : Function.Injective (Fm I) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hinf : ∀ v, FmInf I v h = 1 := fun v => by
    have h0 := congrArg (fun x : I.GA => x.1 v) hh
    simpa [Fm_fst] using h0
  have hfin : FmF I h = 1 := by
    have h0 := congrArg Prod.snd hh
    simpa [Fm_snd] using h0
  have hm : hmat I h = 1 := by
    apply mat_ext
    · intro v
      have hP := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      have h1 := congrArg Formalism.MainNotions.S.uMat (hinf v)
      rw [FmInf_val] at h1
      have h2 : (hmat I h).map (thetaV I v) = I.P v * ofHAInf I h v * (I.P v)⁻¹ := by
        rw [ofHAInf, conj_cancel]
      rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]
      simp [Formalism.MainNotions.S.uMat, Matrix.mul_nonsing_inv _ hP]
    · have h3 : (hmat I h).map (tauF I) = I.fmat (FmF I h) := (FmF_val I h).symm
      rw [h3, hfin, Matrix.map_one _ (map_zero _) (map_one _)]
      simp [Formalism.MainNotions.S.AutInst.fmat]
  apply Subtype.ext
  apply Units.ext
  exact hm

def liftMat (Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (W : Matrix (Fin I.n) (Fin I.n) (EAf I)) : Matrix (Fin I.n) (Fin I.n) (TT I) :=
  fun i j => (TT_surj I (fun v => Z v i j) (W i j)).choose

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(TT_surj I (fun v => Z v i j) (W i j)).choose_spec.1 v`.
-/
theorem liftMat_theta (Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (W : Matrix (Fin I.n) (Fin I.n) (EAf I)) (v : InfinitePlace I.F) :
    (liftMat I Z W).map (thetaV I v) = Z v := by
  ext i j
  exact (TT_surj I (fun v => Z v i j) (W i j)).choose_spec.1 v

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(TT_surj I (fun v => Z v i j) (W i j)).choose_spec.2`.
-/
theorem liftMat_tau (Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (W : Matrix (Fin I.n) (Fin I.n) (EAf I)) : (liftMat I Z W).map (tauF I) = W := by
  ext i j
  exact (TT_surj I (fun v => Z v i j) (W i j)).choose_spec.2

/- English proof (translation)
Introduce `x`. Establish `hPinv : ∀ v, (I.P v)⁻¹ * I.P v = 1` using `fun v => Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))`. Establish `hPinv' : ∀ v, I.P v * (I.P v)⁻¹ = 1` using `fun v => Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))`. Set `Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ` to `fun v => I.P v * uMat (x.1 v) * (I.P v)⁻¹`. Set `Z' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ` to `fun v => I.P v * uMat ((x.1 v)⁻¹) * (I.P v)⁻¹`.

Set `M` to `liftMat I Z (I.fmat x.2)`. Set `M'` to `liftMat I Z' (I.fmat x.2⁻¹)`. Establish `hθ1 : ∀ v, M.map (thetaV I v) = Z v` using `fun v => liftMat_theta I Z (I.fmat x.2) v`. Establish `hθ2 : ∀ v, M'.map (thetaV I v) = Z' v` using `fun v => liftMat_theta I Z' (I.fmat x.2⁻¹) v`. Establish `hτ1 : M.map (tauF I) = I.fmat x.2` using `liftMat_tau I Z (I.fmat x.2)`.

Establish `hτ2 : M'.map (tauF I) = I.fmat x.2⁻¹` using `liftMat_tau I Z' (I.fmat x.2⁻¹)`. Establish `hconj : ∀ v (A B : Matrix (Fin I.n) (Fin I.n) ℂ), A * B = 1 → (I.P v * A * (I.P v)⁻¹) * (I.P v * B * (I.P v)⁻¹) = 1`. Introduce `v A B hAB`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (I.P v)⁻¹ (I.P v), hPinv, Matrix.one_mul, ← Matrix.mul_assoc A B, hAB, Matrix.one_mul, hPinv']`.

Establish `hθone : ∀ v, (1 : Matrix (Fin I.n) (Fin I.n) (TT I)).map (thetaV I v) = 1` using `fun v => Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hτone : (1 : Matrix (Fin I.n) (Fin I.n) (TT I)).map (tauF I) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hMM' : M * M' = 1`. Apply `mat_ext I` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[Matrix.map_mul, hθ1, hθ2, hθone]`. Conclude with `hconj v _ _ (Units.mul_inv _)`. Rewrite using `[Matrix.map_mul, hτ1, hτ2, hτone]`. Conclude with `lat_fmat_mul_inv I x.2`. Establish `hM'M : M' * M = 1`.

Apply `mat_ext I` to reduce the goal to its premises. Introduce `v`. Rewrite using `[Matrix.map_mul, hθ1, hθ2, hθone]`. Conclude with `hconj v _ _ (Units.inv_mul _)`. Rewrite using `[Matrix.map_mul, hτ1, hτ2, hτone]`.

Conclude with `lat_fmat_inv_mul I x.2`. Set `u : GL (Fin I.n) (TT I)` to `⟨M, M', hMM', hM'M⟩`. Establish `hmem : u ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J` using `by show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMas …`. Apply `mat_ext I` to reduce the goal to its premises. Introduce `v`.

Establish `hcT : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (thetaV I v) = (Z v)ᴴ`. Rewrite using `[← hθ1 v]`. Use extensionality with `a b`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, thetaV_sigR, Complex.star_def]`. Establish `hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) = I.J.map (I.φ v)`.

Use extensionality with `a b`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Matrix.map_apply]`. Conclude with `(thetaV_tmul_lemma_2 I v 1 (I.J a b)).trans (by rw [map_one, one_mul])`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hcT, hJ, hθ1]`. Establish `hspec` using `I.P_spec v`.

Establish `hx : (uMat (x.1 v))ᴴ * Formalism.REAL.Jm (I.ε v) * uMat (x.1 v) = Formalism.REAL.Jm (I.ε v)` using `(x.1 v).2`. Establish `hPP : (I.P v)⁻¹ᴴ * (I.P v)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hPinv' v, Matrix.conjTranspose_one]`. Use `show (I.P v * uMat (x.1 v) * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v) * (I.P v)⁻¹) = I.J.map (I.φ v)`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = I.J.map (I.φ v) := by rw [hPP, hPinv', Matrix.one_mul, Matrix.mul_one]`. Establish `hcT : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (tauF I) = Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x.2)`. Rewrite using `[← hτ1]`.

Use extensionality with `a b`. Simplify using `[Formalism.UG.cT, tauF_sigR]`. Establish `hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) = I.J.map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := by`. Use extensionality with `a b`. Simplify using `only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Matrix.map_apply]`.

Conclude with `tauF_tmul_lemma I 1 (I.J a b)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hcT, hJ, hτ1]`. Conclude with `x.2.2`. Use `⟨(⟨u, hmem⟩ : ↥(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J)), ?_⟩` and prove the remaining obligations. Use `Prod.ext (funext fun v => ?_) ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show uMat (FmInf I v _) = uMat (x.1 v)`. Use `(FmInf_val I v _).trans ?_` and prove the remaining obligations. Use `show (I.P v)⁻¹ * M.map (thetaV I v) * I.P v = uMat (x.1 v)`.

Rewrite using `[hθ1]`. Conclude with `conj_cancel' I v _`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hτ1`.
-/
theorem Fm_surjective : Function.Surjective (Fm I) := by
  intro x
  have hPinv : ∀ v, (I.P v)⁻¹ * I.P v = 1 := fun v =>
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have hPinv' : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  let Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ := fun v => I.P v * uMat (x.1 v) * (I.P v)⁻¹
  let Z' : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
    fun v => I.P v * uMat ((x.1 v)⁻¹) * (I.P v)⁻¹
  let M := liftMat I Z (I.fmat x.2)
  let M' := liftMat I Z' (I.fmat x.2⁻¹)
  have hθ1 : ∀ v, M.map (thetaV I v) = Z v := fun v => liftMat_theta I Z (I.fmat x.2) v
  have hθ2 : ∀ v, M'.map (thetaV I v) = Z' v := fun v => liftMat_theta I Z' (I.fmat x.2⁻¹) v
  have hτ1 : M.map (tauF I) = I.fmat x.2 := liftMat_tau I Z (I.fmat x.2)
  have hτ2 : M'.map (tauF I) = I.fmat x.2⁻¹ := liftMat_tau I Z' (I.fmat x.2⁻¹)
  have hconj : ∀ v (A B : Matrix (Fin I.n) (Fin I.n) ℂ), A * B = 1 →
      (I.P v * A * (I.P v)⁻¹) * (I.P v * B * (I.P v)⁻¹) = 1 := by
    intro v A B hAB
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v)⁻¹ (I.P v), hPinv, Matrix.one_mul, ← Matrix.mul_assoc A B, hAB,
      Matrix.one_mul, hPinv']
  have hθone : ∀ v, (1 : Matrix (Fin I.n) (Fin I.n) (TT I)).map (thetaV I v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hτone : (1 : Matrix (Fin I.n) (Fin I.n) (TT I)).map (tauF I) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)

  have hMM' : M * M' = 1 := by
    apply mat_ext I
    · intro v
      rw [Matrix.map_mul, hθ1, hθ2, hθone]
      exact hconj v _ _ (Units.mul_inv _)
    · rw [Matrix.map_mul, hτ1, hτ2, hτone]
      exact lat_fmat_mul_inv I x.2
  have hM'M : M' * M = 1 := by
    apply mat_ext I
    · intro v
      rw [Matrix.map_mul, hθ1, hθ2, hθone]
      exact hconj v _ _ (Units.inv_mul _)
    · rw [Matrix.map_mul, hτ1, hτ2, hτone]
      exact lat_fmat_inv_mul I x.2
  let u : GL (Fin I.n) (TT I) := ⟨M, M', hMM', hM'M⟩

  have hmem : u ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * M =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J
    apply mat_ext I
    · intro v
      have hcT : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map
          (thetaV I v) = (Z v)ᴴ := by
        rw [← hθ1 v]
        ext a b
        simp [Formalism.UG.cT, Matrix.conjTranspose_apply, thetaV_sigR, Complex.star_def]
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (thetaV I v) =
          I.J.map (I.φ v) := by
        ext a b
        simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Matrix.map_apply]
        exact (thetaV_tmul_lemma_2 I v 1 (I.J a b)).trans (by rw [map_one, one_mul])
      rw [Matrix.map_mul, Matrix.map_mul, hcT, hJ, hθ1]
      have hspec := I.P_spec v
      have hx : (uMat (x.1 v))ᴴ * Formalism.REAL.Jm (I.ε v) * uMat (x.1 v) = Formalism.REAL.Jm (I.ε v) := (x.1 v).2
      have hPP : (I.P v)⁻¹ᴴ * (I.P v)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, hPinv' v, Matrix.conjTranspose_one]
      show (I.P v * uMat (x.1 v) * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v) * (I.P v)⁻¹) =
        I.J.map (I.φ v)
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      calc (I.P v)⁻¹ᴴ * ((uMat (x.1 v))ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) *
            (I.P v * uMat (x.1 v) * (I.P v)⁻¹)
          = (I.P v)⁻¹ᴴ * ((uMat (x.1 v))ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * uMat (x.1 v)) *
            (I.P v)⁻¹ := by simp only [Matrix.mul_assoc]
        _ = (I.P v)⁻¹ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ := by rw [hspec, hx]
        _ = ((I.P v)⁻¹ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = I.J.map (I.φ v) := by rw [hPP, hPinv', Matrix.one_mul, Matrix.mul_one]
    · have hcT : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) M).map (tauF I) =
          Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x.2) := by
        rw [← hτ1]
        ext a b
        simp [Formalism.UG.cT, tauF_sigR]
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J).map (tauF I) =
          I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
        ext a b
        simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Matrix.map_apply]
        exact tauF_tmul_lemma I 1 (I.J a b)
      rw [Matrix.map_mul, Matrix.map_mul, hcT, hJ, hτ1]
      exact x.2.2
  refine ⟨(⟨u, hmem⟩ : ↥(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J)), ?_⟩
  refine Prod.ext (funext fun v => ?_) ?_
  · apply Subtype.ext
    apply Units.ext
    show uMat (FmInf I v _) = uMat (x.1 v)
    refine (FmInf_val I v _).trans ?_
    show (I.P v)⁻¹ * M.map (thetaV I v) * I.P v = uMat (x.1 v)
    rw [hθ1]
    exact conj_cancel' I v _
  · apply Subtype.ext
    apply Units.ext
    exact hτ1

/- English proof (translation)
Establish `hm : Continuous (RingHom.mapMatrix (m` using `Fin I.n) f).toMonoidHom := by show Continuous fun M : Matrix (Fin I.n) (Fin I.n) (TT I) => M.map f`. Conclude with `continuous_id.matrix_map hf`. Unfold `Formalism.UG.bc`. Use `first`. Consider the case `exact Continuous.units_map _ hm`.

Consider the case `exact Units.continuous_map hm`.
-/
theorem continuous_bc {R : Type} [CommRing R] [TopologicalSpace R] (f : TT I →+* R)
    (hf : Continuous f) : Continuous (Formalism.UG.bc (n := Fin I.n) f) := by
  have hm : Continuous (RingHom.mapMatrix (m := Fin I.n) f).toMonoidHom := by
    show Continuous fun M : Matrix (Fin I.n) (Fin I.n) (TT I) => M.map f
    exact continuous_id.matrix_map hf
  unfold Formalism.UG.bc
  first
    | exact Continuous.units_map _ hm
    | exact Units.continuous_map hm

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Establish `hb` using `(continuous_bc I (thetaV I v) (continuous_thetaV I v)).comp (continuous_matHom I)`. Use `show Continuous fun h : HAd I => ((MulAut.conj (Pu I v)⁻¹) (Formalism.UG.bc (thetaV I v) (matHom I h)) : GL (Fin I.n) ℂ)`. Simplify using `only [MulAut.conj_apply]`. Conclude with `(continuous_const.mul hb).mul continuous_const`.
-/
theorem continuous_FmInf (v : InfinitePlace I.F) : Continuous (FmInf I v) := by
  refine continuous_induced_rng.2 ?_
  have hb := (continuous_bc I (thetaV I v) (continuous_thetaV I v)).comp (continuous_matHom I)
  show Continuous fun h : HAd I =>
    ((MulAut.conj (Pu I v)⁻¹) (Formalism.UG.bc (thetaV I v) (matHom I h)) : GL (Fin I.n) ℂ)
  simp only [MulAut.conj_apply]
  exact (continuous_const.mul hb).mul continuous_const

/- English proof (translation)
Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, map_one_apply I (tauF I)]`.
-/
theorem tau_entry (M : Matrix (Fin I.n) (Fin I.n) (TT I)) (i j : Fin I.n) :
    (M.map (tauF I) - 1) i j = tauF I ((M - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, map_one_apply I (tauF I)]

/- English proof (translation)
Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, map_one_apply I (thetaV I v)]`.
-/
theorem theta_entry (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (TT I)) (i j : Fin I.n) :
    (M.map (thetaV I v) - 1) i j = thetaV I v ((M - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, map_one_apply I (thetaV I v)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, zero_mem _, by simp⟩`.
-/
theorem zero_mem_CInt (c : ℕ) : (0 : EAf I) ∈ CInt I c := ⟨0, zero_mem _, by simp⟩

/- English proof (translation)
Apply `continuous_of_continuousAt_one (FmF I)` to reduce the goal to its premises. Introduce `U hU`. Rewrite `hU` using `[map_one]`. Take `⟨g, hg, hsub⟩` from `I.topf_basis U hU`. Establish `hmm : 1 ≤ g * mm I ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcont : Continuous fun h : HAd I => hmat I h` using `by show Continuous fun h : HAd I => ((matHom I h : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I))`. Conclude with `Units.continuous_val.comp (continuous_matHom I)`. Establish `hent : ∀ i j, Continuous fun h : HAd I => (hmat I h - 1) i j` using `fun i j => (hcont.sub continuous_const).matrix_elem i j`. Set `V : Set (HAd I)` to `{h | ∀ i j, tauF I ((hmat I h - 1) i j) ∈ CInt I (g * mm I ^ 2)} ∩ {h | ∀ i j, tauF I ((hmat I h⁻¹ - 1) i j) ∈ CInt I (g * mm I ^ 2)}`.

Establish `hV : IsOpen V`. Apply `IsOpen.inter` to reduce the goal to its premises. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_tauCInt I _ hmm).preimage (hent i j)`. Simplify using `only [Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_tauCInt I _ hmm).preimage ((hent i j).comp continuous_inv)`. Establish `hone : hmat I 1 - 1 = 0`. Rewrite using `[← matHom_apply, map_one, Units.val_one, sub_self]`. Establish `h1 : (1 : HAd I) ∈ V`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hone, Matrix.zero_apply, map_zero]`. Conclude with `zero_mem_CInt I _`. Rewrite using `[inv_one, hone, Matrix.zero_apply, map_zero]`. Conclude with `zero_mem_CInt I _`. Rewrite using `[Filter.mem_map]`.

Use `Filter.mem_of_superset (hV.mem_nhds h1) ?_` and prove the remaining obligations. Introduce `h hh`. Establish `hk : FmF I h ∈ KgS I g`. Apply `kgS_of_close I g hg` to reduce the goal to its premises. Introduce `i j`.

Rewrite using `[FmF_val, ofHAFin, tau_entry]`. Conclude with `hh.1 i j`. Introduce `i j`. Rewrite using `[← map_inv, FmF_val, ofHAFin, tau_entry]`. Conclude with `hh.2 i j`.

Conclude with `hsub hk`.
-/
theorem continuous_FmF : Continuous (FmF I) := by
  apply continuous_of_continuousAt_one (FmF I)
  intro U hU
  rw [map_one] at hU
  obtain ⟨g, hg, hsub⟩ := I.topf_basis U hU
  have hmm : 1 ≤ g * mm I ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ g * mm I ^ 2 := Nat.mul_le_mul hg (Nat.one_le_pow _ _ (mm_pos I))
  have hcont : Continuous fun h : HAd I => hmat I h := by
    show Continuous fun h : HAd I =>
      ((matHom I h : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I))
    exact Units.continuous_val.comp (continuous_matHom I)
  have hent : ∀ i j, Continuous fun h : HAd I => (hmat I h - 1) i j := fun i j =>
    (hcont.sub continuous_const).matrix_elem i j

  let V : Set (HAd I) := {h | ∀ i j, tauF I ((hmat I h - 1) i j) ∈ CInt I (g * mm I ^ 2)} ∩
    {h | ∀ i j, tauF I ((hmat I h⁻¹ - 1) i j) ∈ CInt I (g * mm I ^ 2)}
  have hV : IsOpen V := by
    apply IsOpen.inter
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_tauCInt I _ hmm).preimage (hent i j)
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (isOpen_tauCInt I _ hmm).preimage ((hent i j).comp continuous_inv)
  have hone : hmat I 1 - 1 = 0 := by
    rw [← matHom_apply, map_one, Units.val_one, sub_self]
  have h1 : (1 : HAd I) ∈ V := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hone, Matrix.zero_apply, map_zero]
      exact zero_mem_CInt I _
    · rw [inv_one, hone, Matrix.zero_apply, map_zero]
      exact zero_mem_CInt I _
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hV.mem_nhds h1) ?_
  intro h hh
  have hk : FmF I h ∈ KgS I g := by
    apply kgS_of_close I g hg
    · intro i j
      rw [FmF_val, ofHAFin, tau_entry]
      exact hh.1 i j
    · intro i j
      rw [← map_inv, FmF_val, ofHAFin, tau_entry]
      exact hh.2 i j
  exact hsub hk

/- English proof (translation)
Establish `h1 : Continuous fun h : HAd I => fun v => FmInf I v h` using `continuous_pi fun v => continuous_FmInf I v`. Establish `h2` using `continuous_FmF I`. Use `first`. Consider the case `exact h1.prodMk h2`. Consider the case `exact h1.prod_mk h2`.
-/
theorem continuous_Fm : Continuous (Fm I) := by
  have h1 : Continuous fun h : HAd I => fun v => FmInf I v h := continuous_pi fun v => continuous_FmInf I v
  have h2 := continuous_FmF I
  first
    | exact h1.prodMk h2
    | exact h1.prod_mk h2

def FmEquiv : HAd I ≃* I.GA := MulEquiv.ofBijective (Fm I) ⟨Fm_injective I, Fm_surjective I⟩

/- English proof (translation)
Use `first`. Consider the case `exact (FmEquiv I).apply_symm_apply x`. Consider the case `exact MulEquiv.ofBijective_apply_symm_apply _ _ x`.
-/
theorem Fm_FmEquiv_symm (x : I.GA) : Fm I ((FmEquiv I).symm x) = x := by
  first
    | exact (FmEquiv I).apply_symm_apply x
    | exact MulEquiv.ofBijective_apply_symm_apply _ _ x

/- English proof (translation)
Use `⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Formalism.UG.stabGL I.Lf).one_mem`. Establish `h1 : I.fmat 1 = 1` using `by simp [Formalism.MainNotions.S.AutInst.fmat]`. Rewrite using `[h1, sub_self, Matrix.zero_mulVec, smul_zero]`.
-/
theorem one_mem_KgS (g : ℕ) : (1 : I.Gf) ∈ KgS I g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  · exact (Formalism.UG.stabGL I.Lf).one_mem
  · have h1 : I.fmat 1 = 1 := by simp [Formalism.MainNotions.S.AutInst.fmat]
    rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

/- English proof (translation)
Establish `hsymm1 : (FmEquiv I).symm 1 = 1` using `map_one _`. Establish `hθ : ∀ x : I.GA, ∀ v, thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j) = (I.P v * uMat (x.1 v) * (I.P v)⁻¹ - 1) i j`. Introduce `x v`. Rewrite using `[← theta_entry]`. Use `congr 2`.

Establish `h1 : uMat (FmInf I v ((FmEquiv I).symm x)) = ofHAInf I ((FmEquiv I).symm x) v` using `FmInf_val I v _`. Establish `h2 : FmInf I v ((FmEquiv I).symm x) = x.1 v`. Rewrite using `[← Fm_fst, Fm_FmEquiv_symm]`. Rewrite `h1` using `[h2]`. Rewrite using `[h1, ofHAInf, conj_cancel]`.

Establish `hτ : ∀ x : I.GA, tauF I ((hmat I ((FmEquiv I).symm x) - 1) i j) = (I.fmat x.2 - 1) i j`. Introduce `x`. Rewrite using `[← tau_entry]`. Use `congr 2`. Establish `h2 : FmF I ((FmEquiv I).symm x) = x.2`.

Rewrite using `[← Fm_snd, Fm_FmEquiv_symm]`. Rewrite using `[← h2, FmF_val, ofHAFin]`. Establish `hone : hmat I 1 = 1`. Rewrite using `[← matHom_apply, map_one, Units.val_one]`. Introduce `W' hW'`.

Simplify using `only at hW'`. Rewrite `hW'` using `[hsymm1, hone]`. Establish `hW : {y : TT I | y + (1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j ∈ W'} ∈ nhds (0 : TT I)` using `(continuous_add_right ((1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j)).continuousAt.preimage_mem_nhds (by rw [zero_add]; exact hW')`. Take `⟨δ, hδ, c, hc1, hsmall⟩` from `tt_small I _ hW`. Establish `hmm : 1 ≤ c * mm I ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcontv : ∀ v, Continuous fun x : I.GA => thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j)`. Introduce `v`. Repeatedly rewrite using `[hθ]`. Establish `hu : Continuous fun x : I.GA => uMat (x.1 v)` using `(Units.continuous_val.comp continuous_subtype_val).comp ((continuous_apply v).comp continuous_fst)`.

Conclude with `(((continuous_const.mul hu).mul continuous_const).sub continuous_const).matrix_elem i j`. Set `V : Set I.GA` to `{x | ∀ v, ‖thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j)‖ < δ} ∩ {x | x.2 ∈ KgS I (c * mm I ^ 2)}`. Establish `hV : IsOpen V`. Apply `IsOpen.inter` to reduce the goal to its premises. Simplify using `only [Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun v => isOpen_lt (hcontv v).norm continuous_const`. Conclude with `(I.topf_open _ hmm).preimage continuous_snd`. Establish `h1V : (1 : I.GA) ∈ V`. Use `⟨fun v => ?_, one_mem_KgS I _⟩` and prove the remaining obligations. Establish `hu1 : uMat ((1 : I.GA).1 v) = 1` using `rfl`.

Establish `hPP : I.P v * 1 * (I.P v)⁻¹ = 1`. Rewrite using `[Matrix.mul_one]`. Conclude with `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))`. Rewrite using `[hθ, hu1, hPP, sub_self, Matrix.zero_apply, norm_zero]`. Conclude with `hδ`.

Rewrite using `[Filter.mem_map]`. Use `Filter.mem_of_superset (hV.mem_nhds h1V) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hy` using `hsmall _ hx.1 (by rw [hτ]; exact (close_of_kgS I c hc1 x.2 hx.2 i j).1)`. Use `show hmat I ((FmEquiv I).symm x) i j ∈ W'`.

Establish `e : (hmat I ((FmEquiv I).symm x) - 1) i j + (1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j = hmat I ((FmEquiv I).symm x) i j`. Rewrite using `[Matrix.sub_apply, sub_add_cancel]`. Rewrite using `[← e]`. Conclude with `hy`.
-/
theorem continuousAt_entry (i j : Fin I.n) :
    ContinuousAt (fun x : I.GA => hmat I ((FmEquiv I).symm x) i j) 1 := by
  have hsymm1 : (FmEquiv I).symm 1 = 1 := map_one _

  have hθ : ∀ x : I.GA, ∀ v, thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j) =
      (I.P v * uMat (x.1 v) * (I.P v)⁻¹ - 1) i j := by
    intro x v
    rw [← theta_entry]
    congr 2
    have h1 : uMat (FmInf I v ((FmEquiv I).symm x)) = ofHAInf I ((FmEquiv I).symm x) v := FmInf_val I v _
    have h2 : FmInf I v ((FmEquiv I).symm x) = x.1 v := by
      rw [← Fm_fst, Fm_FmEquiv_symm]
    rw [h2] at h1
    rw [h1, ofHAInf, conj_cancel]
  have hτ : ∀ x : I.GA, tauF I ((hmat I ((FmEquiv I).symm x) - 1) i j) = (I.fmat x.2 - 1) i j := by
    intro x
    rw [← tau_entry]
    congr 2
    have h2 : FmF I ((FmEquiv I).symm x) = x.2 := by
      rw [← Fm_snd, Fm_FmEquiv_symm]
    rw [← h2, FmF_val, ofHAFin]
  have hone : hmat I 1 = 1 := by
    rw [← matHom_apply, map_one, Units.val_one]
  intro W' hW'
  dsimp only at hW'
  rw [hsymm1, hone] at hW'

  have hW : {y : TT I | y + (1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j ∈ W'} ∈ nhds (0 : TT I) :=
    (continuous_add_right ((1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j)).continuousAt.preimage_mem_nhds
      (by rw [zero_add]; exact hW')
  obtain ⟨δ, hδ, c, hc1, hsmall⟩ := tt_small I _ hW
  have hmm : 1 ≤ c * mm I ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ c * mm I ^ 2 := Nat.mul_le_mul hc1 (Nat.one_le_pow _ _ (mm_pos I))
  have hcontv : ∀ v, Continuous fun x : I.GA => thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j) := by
    intro v
    simp_rw [hθ]
    have hu : Continuous fun x : I.GA => uMat (x.1 v) :=
      (Units.continuous_val.comp continuous_subtype_val).comp ((continuous_apply v).comp continuous_fst)
    exact (((continuous_const.mul hu).mul continuous_const).sub continuous_const).matrix_elem i j
  let V : Set I.GA := {x | ∀ v, ‖thetaV I v ((hmat I ((FmEquiv I).symm x) - 1) i j)‖ < δ} ∩
    {x | x.2 ∈ KgS I (c * mm I ^ 2)}
  have hV : IsOpen V := by
    apply IsOpen.inter
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun v => isOpen_lt (hcontv v).norm continuous_const
    · exact (I.topf_open _ hmm).preimage continuous_snd
  have h1V : (1 : I.GA) ∈ V := by
    refine ⟨fun v => ?_, one_mem_KgS I _⟩
    have hu1 : uMat ((1 : I.GA).1 v) = 1 := rfl
    have hPP : I.P v * 1 * (I.P v)⁻¹ = 1 := by
      rw [Matrix.mul_one]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    rw [hθ, hu1, hPP, sub_self, Matrix.zero_apply, norm_zero]
    exact hδ
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
  intro x hx
  have hy := hsmall _ hx.1 (by rw [hτ]; exact (close_of_kgS I c hc1 x.2 hx.2 i j).1)
  show hmat I ((FmEquiv I).symm x) i j ∈ W'
  have e : (hmat I ((FmEquiv I).symm x) - 1) i j + (1 : Matrix (Fin I.n) (Fin I.n) (TT I)) i j =
      hmat I ((FmEquiv I).symm x) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [← e]
  exact hy

/- English proof (translation)
Set `matF : HAd I → GL (Fin I.n) (TT I)` to `fun h => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h`. Establish `hind : Topology.IsInducing ((Units.embedProduct (Matrix (Fin I.n) (Fin I.n) (TT I))) ∘ matF)` using `Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal`. Apply the tactic sequence `have hentinv : ∀ i j, ContinuousAt (fun x : I.GA => hmat I ((FmEquiv I).symm x⁻¹) i j) 1 := fun i j => (continuousAt_entry I i j).comp_of_eq continuous_inv.continuousAt inv_one`. Establish `hat : ContinuousAt (FmEquiv I).symm 1`. Rewrite using `[hind.continuousAt_iff]`.

Use `show ContinuousAt (fun x : I.GA => ((((matF ((FmEquiv I).symm x)) : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I)), MulOpposite.op (((matF ((FmEquiv I).symm x))⁻¹ : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I)))) 1`. Apply `ContinuousAt.prodMk` to reduce the goal to its premises. Apply the tactic sequence `exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => continuousAt_entry I i j`. Apply `MulOpposite.continuous_op.continuousAt.comp` to reduce the goal to its premises. Establish `e : (fun x : I.GA => (((matF ((FmEquiv I).symm x))⁻¹ : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I))) = fun x => hmat I ((FmEquiv I).symm x⁻¹)`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => hentinv i j`.

Conclude with `continuous_of_continuousAt_one (FmEquiv I).symm.toMonoidHom hat`.
-/
theorem continuous_FmEquiv_symm : Continuous (FmEquiv I).symm := by
  let matF : HAd I → GL (Fin I.n) (TT I) := fun h =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h
  have hind : Topology.IsInducing ((Units.embedProduct (Matrix (Fin I.n) (Fin I.n) (TT I))) ∘ matF) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  have hentinv : ∀ i j, ContinuousAt (fun x : I.GA => hmat I ((FmEquiv I).symm x⁻¹) i j) 1 := fun i j =>
    (continuousAt_entry I i j).comp_of_eq continuous_inv.continuousAt inv_one
  have hat : ContinuousAt (FmEquiv I).symm 1 := by
    rw [hind.continuousAt_iff]
    show ContinuousAt (fun x : I.GA =>
      ((((matF ((FmEquiv I).symm x)) : GL (Fin I.n) (TT I)) : Matrix (Fin I.n) (Fin I.n) (TT I)),
        MulOpposite.op (((matF ((FmEquiv I).symm x))⁻¹ : GL (Fin I.n) (TT I)) :
          Matrix (Fin I.n) (Fin I.n) (TT I)))) 1
    apply ContinuousAt.prodMk
    · exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => continuousAt_entry I i j
    · apply MulOpposite.continuous_op.continuousAt.comp
      have e : (fun x : I.GA => (((matF ((FmEquiv I).symm x))⁻¹ : GL (Fin I.n) (TT I)) :
          Matrix (Fin I.n) (Fin I.n) (TT I))) = fun x => hmat I ((FmEquiv I).symm x⁻¹) := by
        funext x
        rw [map_inv]
        rfl
      rw [e]
      exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => hentinv i j
  exact continuous_of_continuousAt_one (FmEquiv I).symm.toMonoidHom hat

def bridge : I.GA ≃ₜ* HAd I where
  toMulEquiv := (FmEquiv I).symm
  continuous_toFun := continuous_FmEquiv_symm I
  continuous_invFun := continuous_Fm I

/- English proof (translation)
Introduce `x`. Establish `hx` using `Fm_FmEquiv_symm I x`. Use `⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← hx]`. Conclude with `FmInf_val I v _`.

Use `conv_lhs => rw [← hx]`. Conclude with `FmF_val I _`.
-/
theorem bridge_isBridge : IsBridge I (bridge I) := by
  intro x
  have hx := Fm_FmEquiv_symm I x
  refine ⟨fun v => ?_, ?_⟩
  · conv_lhs => rw [← hx]
    exact FmInf_val I v _
  · conv_lhs => rw [← hx]
    exact FmF_val I _

/- English proof (translation)
Unfold `AdBridgeIso`. Conclude with `⟨bridge I, bridge_isBridge I⟩`.
-/
theorem adelic_isomorphism_exists : AdBridgeIso I := by
  unfold AdBridgeIso
  exact ⟨bridge I, bridge_isBridge I⟩

/- English proof (translation)
Unfold `AdelicIsomorphism`. Conclude with `⟨adelic_isomorphism_exists I, hGF, hK⟩`.
-/
theorem adelic_isomorphism_of_parts (hGF : AdBridgeGF I) (hK : AdBridgeK I) : AdelicIsomorphism I := by
  unfold AdelicIsomorphism
  exact ⟨adelic_isomorphism_exists I, hGF, hK⟩

end Formalism.L2.SG.Pf
