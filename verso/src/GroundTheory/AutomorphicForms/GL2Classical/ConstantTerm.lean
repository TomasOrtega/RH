import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.IsWeightLevelAdelicLift
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

instance : Unique (UPos 2 1) where
  default := ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩
  uniq p := by
    obtain ⟨⟨i, j⟩, hi, hj⟩ := p
    have hj2 := j.isLt
    have hi' : (i : ℕ) < 1 := hi
    have hj' : 1 ≤ (j : ℕ) := hj
    refine Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · show (i : ℕ) = 0
      omega
    · show (j : ℕ) = 1
      omega

def unipAdele (x : 𝔸[ℚ]) : AdelicGL ℚ 2 := unipGL (n := 2) (r := 1) fun _ => x

def unipReal (t : ℝ) : GL (Fin 2) ℝ := unipGL (n := 2) (r := 1) fun _ => t

def unipFin (y : 𝔸f) : FiniteAdelicGL ℚ 2 := unipGL (n := 2) (r := 1) fun _ => y

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [unipMatrix, blockEntry_apply]`.
-/
theorem unipMatrix_apply {R : Type*} [CommRing R] (x : R) (a b : Fin 2) :
    unipMatrix (n := 2) (r := 1) (fun _ => x) a b = if a = 0 ∧ b = 1 then x else if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [unipMatrix, blockEntry_apply]

/- English proof (translation)
The claim follows from `unipGL_add (n := 2) (r := 1) (fun _ => x) (fun _ => y)`.
-/
theorem unipAdele_add (x y : 𝔸[ℚ]) : unipAdele (x + y) = unipAdele x * unipAdele y :=
  unipGL_add (n := 2) (r := 1) (fun _ => x) (fun _ => y)

/- English proof (translation)
The claim follows from `unipGL_add (n := 2) (r := 1) (fun _ => s) (fun _ => t)`.
-/
theorem unipReal_add (s t : ℝ) : unipReal (s + t) = unipReal s * unipReal t :=
  unipGL_add (n := 2) (r := 1) (fun _ => s) (fun _ => t)

/- English proof (translation)
The claim follows from `(diagonal_unipGL (K := ℚ) (n := 2) (r := 1) fun _ => q).symm`.
-/
theorem unipAdele_algebraMap (q : ℚ) :
    unipAdele (algebraMap ℚ 𝔸[ℚ] q) = diagonal ℚ 2 (unipGL (n := 2) (r := 1) fun _ => q) :=
  (diagonal_unipGL (K := ℚ) (n := 2) (r := 1) fun _ => q).symm

/- English proof (translation)
The claim follows from `RingHom.congr_fun (RingHom.ext_rat (RationalIdeles.realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) (Rat.castHom ℝ)) q`.
-/
theorem realEquiv_algebraMap (q : ℚ) :
    RationalIdeles.realEquiv (algebraMap ℚ (InfiniteAdeleRing ℚ) q) = q :=
  RingHom.congr_fun (RingHom.ext_rat (RationalIdeles.realEquiv.toRingHom.comp
    (algebraMap ℚ (InfiniteAdeleRing ℚ))) (Rat.castHom ℝ)) q

/- English proof (translation)
Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Rewrite using `[map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Use `Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (Units.ext (Matrix.ext fun a b => ?_))` and prove the remaining obligations. Rewrite using `[prodEquiv_apply_fst]`. Express the relevant statement in the definitionally equal form `(unipMatrix (n := 2) (r := 1) (fun _ => x) a b).1 = RationalIdeles.realEquiv.symm (unipMatrix (n := 2) (r := 1) (fun _ => RationalIdeles.realEquiv x.1) a b)`.

Rewrite using `[unipMatrix_apply, unipMatrix_apply]`. Use `split_ifs`. Conclude with `(RationalIdeles.realEquiv.symm_apply_apply _).symm`. Conclude with `(map_one RationalIdeles.realEquiv.symm).symm`. Conclude with `(map_zero RationalIdeles.realEquiv.symm).symm`.

Rewrite using `[prodEquiv_apply_snd]`. Express the relevant statement in the definitionally equal form `(unipMatrix (n := 2) (r := 1) (fun _ => x) a b).2 = unipMatrix (n := 2) (r := 1) (fun _ => x.2) a b`. Rewrite using `[unipMatrix_apply, unipMatrix_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem unipAdele_eq (x : 𝔸[ℚ]) :
    unipAdele x = realEmb (unipReal (RationalIdeles.realEquiv x.1)) * finEmb ℚ 2 (unipFin x.2) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (Units.ext (Matrix.ext fun a b => ?_))
  · rw [prodEquiv_apply_fst]
    change (unipMatrix (n := 2) (r := 1) (fun _ => x) a b).1 =
      RationalIdeles.realEquiv.symm (unipMatrix (n := 2) (r := 1)
        (fun _ => RationalIdeles.realEquiv x.1) a b)
    rw [unipMatrix_apply, unipMatrix_apply]
    split_ifs
    · exact (RationalIdeles.realEquiv.symm_apply_apply _).symm
    · exact (map_one RationalIdeles.realEquiv.symm).symm
    · exact (map_zero RationalIdeles.realEquiv.symm).symm
  · rw [prodEquiv_apply_snd]
    change (unipMatrix (n := 2) (r := 1) (fun _ => x) a b).2 =
      unipMatrix (n := 2) (r := 1) (fun _ => x.2) a b
    rw [unipMatrix_apply, unipMatrix_apply]
    split_ifs <;> rfl

/- English proof (translation)
Establish `hmp` using `measurePreserving_funUnique (adeleMeasure ℚ) (UPos 2 1)`. Rewrite using `[constantTerm, ← hmp.setIntegral_preimage_emb (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[ℚ]).measurableEmbedding]`. Establish `hset : (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[ℚ]) ⁻¹' fundamentalSet ℚ = unipFundamentalDomain ℚ 2 1`. Use extensionality with `X`. Simplify using `only [Set.mem_preimage, MeasurableEquiv.funUnique_apply, unipFundamentalDomain, Set.mem_pi, Set.mem_univ, true_implies]`.

Prove the components needed by the constructor for the conclusion. Introduce `h p`. Rewrite using `[Unique.eq_default p]` and apply the resulting hypothesis. Introduce `h`. Conclude with `h default`.

Rewrite using `[hset]`. Use `setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X _ => ?_` and prove the remaining obligations. Establish `: (fun _ : UPos 2 1 => X default) = X` using `funext fun p => by rw [Unique.eq_default p]`. Simplify using `only [MeasurableEquiv.funUnique_apply, unipAdele, this]`.
-/
theorem constantTerm_eq_setIntegral_fundamentalSet (φ : AdelicGL ℚ 2 → ℂ) (g : AdelicGL ℚ 2) :
    constantTerm 1 φ g = ∫ x in fundamentalSet ℚ, φ (unipAdele x * g) ∂adeleMeasure ℚ := by
  have hmp := measurePreserving_funUnique (adeleMeasure ℚ) (UPos 2 1)
  rw [constantTerm, ← hmp.setIntegral_preimage_emb (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[ℚ]).measurableEmbedding]
  have hset : (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[ℚ]) ⁻¹' fundamentalSet ℚ =
      unipFundamentalDomain ℚ 2 1 := by
    ext X
    simp only [Set.mem_preimage, MeasurableEquiv.funUnique_apply, unipFundamentalDomain,
      Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h p
      rwa [Unique.eq_default p]
    · intro h
      exact h default
  rw [hset]
  refine setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X _ => ?_
  have : (fun _ : UPos 2 1 => X default) = X := funext fun p => by rw [Unique.eq_default p]
  simp only [MeasurableEquiv.funUnique_apply, unipAdele, this]

instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  Set.Countable.to_subtype ((Set.countable_range (algebraMap ℚ 𝔸[ℚ])).mono fun _ hx => hx)

/- English proof (translation)
Rewrite using `[constantTerm_eq_setIntegral_fundamentalSet]`. Use `(isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq hD fun ξ x => ?_` and prove the remaining obligations. Take `⟨_, q, rfl⟩` from `ξ`. Express the relevant statement in the definitionally equal form `φ (unipAdele (algebraMap ℚ 𝔸[ℚ] q + x) * g) = _`. Rewrite using `[unipAdele_add, unipAdele_algebraMap, mul_assoc, hφ]`.
-/
theorem constantTerm_eq_setIntegral_adele {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsLeftInvariant φ)
    {D : Set 𝔸[ℚ]}
    (hD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) D (adeleMeasure ℚ))
    (g : AdelicGL ℚ 2) :
    constantTerm 1 φ g = ∫ x in D, φ (unipAdele x * g) ∂adeleMeasure ℚ := by
  rw [constantTerm_eq_setIntegral_fundamentalSet]
  refine (isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq hD fun ξ x => ?_
  obtain ⟨_, q, rfl⟩ := ξ
  change φ (unipAdele (algebraMap ℚ 𝔸[ℚ] q + x) * g) = _
  rw [unipAdele_add, unipAdele_algebraMap, mul_assoc, hφ]

def realHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toEquiv := RationalIdeles.realEquiv.toEquiv
  continuous_toFun := RationalIdeles.continuous_realEquiv
  continuous_invFun := RationalIdeles.continuous_realEquiv_symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realHomeomorph_apply (x : InfiniteAdeleRing ℚ) :
    realHomeomorph x = RationalIdeles.realEquiv x :=
  rfl

variable (N : ℕ) [NeZero N]

def levelDomain : Set 𝔸[ℚ] :=
  (RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) N) ×ˢ levelIdeal N

/- English proof (translation)
The claim follows from `(isOpen_levelIdeal N).measurableSet`.
-/
theorem measurableSet_levelIdeal : MeasurableSet (levelIdeal N) :=
  (isOpen_levelIdeal N).measurableSet

/- English proof (translation)
The claim follows from `(measurableSet_Ico.preimage realHomeomorph.continuous.measurable).prod (measurableSet_levelIdeal N)`.
-/
theorem measurableSet_levelDomain : MeasurableSet (levelDomain N) :=
  (measurableSet_Ico.preimage realHomeomorph.continuous.measurable).prod (measurableSet_levelIdeal N)

variable {N} in
/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `hx`. Take `⟨t, ht, rfl⟩` from `hy`. Conclude with `⟨s - t, sub_mem hs ht, by rw [mul_sub]⟩`.
-/
theorem sub_mem_levelIdeal {x y : 𝔸f} (hx : x ∈ levelIdeal N) (hy : y ∈ levelIdeal N) :
    x - y ∈ levelIdeal N := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨s - t, sub_mem hs ht, by rw [mul_sub]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨m, intCast_mem_integralFiniteAdeles m, rfl⟩`.
-/
theorem natCast_mul_intCast_mem_levelIdeal (m : ℤ) : (N : 𝔸f) * (m : 𝔸f) ∈ levelIdeal N :=
  ⟨m, intCast_mem_integralFiniteAdeles m, rfl⟩

/- English proof (translation)
Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `mul_mem (natCast_mem _ N) ht`.
-/
theorem levelIdeal_subset : levelIdeal N ⊆ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set 𝔸f) := by
  rintro _ ⟨t, ht, rfl⟩
  exact mul_mem (natCast_mem _ N) ht

/- English proof (translation)
Use `IsAddFundamentalDomain.mk' (measurableSet_levelDomain N).nullMeasurableSet fun a => ?_` and prove the remaining obligations. Establish `hN : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)`. Choose the witnesses or unpack the hypotheses as in `⟨q₀, hq₀⟩ : ∃ q₀ : ℚ, a.2 + algebraMap ℚ 𝔸f q₀ ∈ levelIdeal N := by`. Establish `hopen : IsOpen ((fun y : 𝔸f => a.2 + y) ⁻¹' levelIdeal N)` using `(isOpen_levelIdeal N).preimage (continuous_const.add continuous_id)`. Establish `hne : ((fun y : 𝔸f => a.2 + y) ⁻¹' levelIdeal N).Nonempty` using `⟨-a.2, by simpa using zero_mem_levelIdeal N⟩`.

Take `⟨_, hy, q₀, rfl⟩` from `(AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).inter_open_nonempty _ hopen hne`. Conclude with `⟨q₀, hy⟩`. Use `set r : ℝ := RationalIdeles.realEquiv a.1 + q₀`. Use `set m : ℤ := ⌊r / N⌋`. Use `set q : ℚ := q₀ - N * m`.

Establish `hreal : ∀ q' : ℚ, ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).1) = algebraMap ℚ (InfiniteAdeleRing ℚ) q' + a.1` using `fun _ => rfl`. Establish `hfin : ∀ q' : ℚ, ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).2) = algebraMap ℚ 𝔸f q' + a.2` using `fun _ => rfl`. Use `⟨⟨algebraMap ℚ 𝔸[ℚ] q, q, rfl⟩, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N`. Rewrite using `[hreal, map_add, realEquiv_algebraMap]`.

Establish `h1 : (m : ℝ) ≤ r / N` using `Int.floor_le _`. Establish `h2 : r / N < m + 1` using `Int.lt_floor_add_one _`. Rewrite `h1` using `[le_div_iff₀ hN]`. Rewrite `h2` using `[div_lt_iff₀ hN]`. Simplify using `only [q, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]`.

Apply the tactic sequence `constructor <;> nlinarith`. Express the relevant statement in the definitionally equal form `(algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).2 ∈ levelIdeal N`. Rewrite using `[hfin]`. Establish `: algebraMap ℚ 𝔸f q + a.2 = (a.2 + algebraMap ℚ 𝔸f q₀) - (N : 𝔸f) * (m : 𝔸f)`. Simplify using `only [q, map_sub, map_mul, map_natCast, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `sub_mem_levelIdeal hq₀ (natCast_mul_intCast_mem_levelIdeal N m)`. Introduce and unpack `⟨_, q', rfl⟩ ⟨hr', hf'⟩`. Establish `hr : RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N`.

Rewrite using `[hreal, map_add, realEquiv_algebraMap]`. Establish `h1 : (m : ℝ) ≤ r / N` using `Int.floor_le _`. Establish `h2 : r / N < m + 1` using `Int.lt_floor_add_one _`. Rewrite `h1` using `[le_div_iff₀ hN]`. Rewrite `h2` using `[div_lt_iff₀ hN]`.

Simplify using `only [q, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]`. Apply the tactic sequence `constructor <;> nlinarith`. Establish `hf : (algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).2 ∈ levelIdeal N`. Rewrite using `[hfin]`. Establish `: algebraMap ℚ 𝔸f q + a.2 = (a.2 + algebraMap ℚ 𝔸f q₀) - (N : 𝔸f) * (m : 𝔸f)`.

Simplify using `only [q, map_sub, map_mul, map_natCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `sub_mem_levelIdeal hq₀ (natCast_mul_intCast_mem_levelIdeal N m)`. Express the relevant statement in the definitionally equal form `RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N at hr'`.

Express the relevant statement in the definitionally equal form `(algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).2 ∈ levelIdeal N at hf'`. Rewrite `hr`, `hr'` using `[hreal, map_add, realEquiv_algebraMap]`. Rewrite `hf`, `hf'` using `[hfin]`. Establish `hdiff` using `sub_mem_levelIdeal hf' hf`. Rewrite `hdiff` using `[add_sub_add_right_eq_sub, ← map_sub]`.

Take `⟨m', hm'⟩` from `exists_int_of_mem_levelIdeal N hdiff`. Establish `hm'0 : m' = 0`. Establish `hmr : ((q' - q : ℚ) : ℝ) = N * m'` using `by rw [hm']; push_cast; ring`. Move the coercions through the operations in `at hmr`. Establish `hlt : |(N : ℝ) * m'| < N`.

Rewrite using `[← hmr, abs_lt]`. Apply the tactic sequence `constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]`. Rewrite `hlt` using `[abs_mul, Nat.abs_cast]`. Establish `: |(m' : ℝ)| < 1`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Use the polynomial consequences of the given equalities and inequalities. Establish `: |m'| < 1` using `by exact_mod_cast this`. Conclude with `Int.abs_lt_one_iff.1 this`. Establish `: q' = q`.

Rewrite `hm'` using `[hm'0, Int.cast_zero, mul_zero, sub_eq_zero]`. Conclude with `hm'`. Conclude with `Subtype.ext (by simp only [this])`.
-/
theorem isAddFundamentalDomain_levelDomain :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (levelDomain N) (adeleMeasure ℚ) := by
  refine IsAddFundamentalDomain.mk' (measurableSet_levelDomain N).nullMeasurableSet fun a => ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℚ, a.2 + algebraMap ℚ 𝔸f q₀ ∈ levelIdeal N := by
    have hopen : IsOpen ((fun y : 𝔸f => a.2 + y) ⁻¹' levelIdeal N) :=
      (isOpen_levelIdeal N).preimage (continuous_const.add continuous_id)
    have hne : ((fun y : 𝔸f => a.2 + y) ⁻¹' levelIdeal N).Nonempty :=
      ⟨-a.2, by simpa using zero_mem_levelIdeal N⟩
    obtain ⟨_, hy, q₀, rfl⟩ :=
      (AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).inter_open_nonempty _ hopen hne
    exact ⟨q₀, hy⟩

  set r : ℝ := RationalIdeles.realEquiv a.1 + q₀
  set m : ℤ := ⌊r / N⌋
  set q : ℚ := q₀ - N * m
  have hreal : ∀ q' : ℚ, ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).1) =
      algebraMap ℚ (InfiniteAdeleRing ℚ) q' + a.1 := fun _ => rfl
  have hfin : ∀ q' : ℚ, ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).2) = algebraMap ℚ 𝔸f q' + a.2 :=
    fun _ => rfl
  refine ⟨⟨algebraMap ℚ 𝔸[ℚ] q, q, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · change RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N
    rw [hreal, map_add, realEquiv_algebraMap]
    have h1 : (m : ℝ) ≤ r / N := Int.floor_le _
    have h2 : r / N < m + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hN] at h1
    rw [div_lt_iff₀ hN] at h2
    simp only [q, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
    constructor <;> nlinarith
  · change (algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).2 ∈ levelIdeal N
    rw [hfin]
    have : algebraMap ℚ 𝔸f q + a.2 = (a.2 + algebraMap ℚ 𝔸f q₀) - (N : 𝔸f) * (m : 𝔸f) := by
      simp only [q, map_sub, map_mul, map_natCast, map_intCast]
      ring
    rw [this]
    exact sub_mem_levelIdeal hq₀ (natCast_mul_intCast_mem_levelIdeal N m)
  · rintro ⟨_, q', rfl⟩ ⟨hr', hf'⟩
    have hr : RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N := by
      rw [hreal, map_add, realEquiv_algebraMap]
      have h1 : (m : ℝ) ≤ r / N := Int.floor_le _
      have h2 : r / N < m + 1 := Int.lt_floor_add_one _
      rw [le_div_iff₀ hN] at h1
      rw [div_lt_iff₀ hN] at h2
      simp only [q, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
      constructor <;> nlinarith
    have hf : (algebraMap ℚ 𝔸[ℚ] q + a : 𝔸[ℚ]).2 ∈ levelIdeal N := by
      rw [hfin]
      have : algebraMap ℚ 𝔸f q + a.2 = (a.2 + algebraMap ℚ 𝔸f q₀) - (N : 𝔸f) * (m : 𝔸f) := by
        simp only [q, map_sub, map_mul, map_natCast, map_intCast]
        ring
      rw [this]
      exact sub_mem_levelIdeal hq₀ (natCast_mul_intCast_mem_levelIdeal N m)
    change RationalIdeles.realEquiv ((algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).1) ∈ Set.Ico (0 : ℝ) N at hr'
    change (algebraMap ℚ 𝔸[ℚ] q' + a : 𝔸[ℚ]).2 ∈ levelIdeal N at hf'
    rw [hreal, map_add, realEquiv_algebraMap] at hr hr'
    rw [hfin] at hf hf'
    have hdiff := sub_mem_levelIdeal hf' hf
    rw [add_sub_add_right_eq_sub, ← map_sub] at hdiff
    obtain ⟨m', hm'⟩ := exists_int_of_mem_levelIdeal N hdiff
    have hm'0 : m' = 0 := by
      have hmr : ((q' - q : ℚ) : ℝ) = N * m' := by rw [hm']; push_cast; ring
      push_cast at hmr
      have hlt : |(N : ℝ) * m'| < N := by
        rw [← hmr, abs_lt]
        constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
      rw [abs_mul, Nat.abs_cast] at hlt
      have : |(m' : ℝ)| < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have : |m'| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.1 this
    have : q' = q := by
      rw [hm'0, Int.cast_zero, mul_zero, sub_eq_zero] at hm'
      exact hm'
    exact Subtype.ext (by simp only [this])

variable {N} in

/- English proof (translation)
Establish `hyZ : y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `levelIdeal_subset N hy`. Establish `hu : unipFin y ∈ integralFiniteGL ℚ 2`. Rewrite using `[mem_integralFiniteGL_iff]`. Use `⟨fun a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => y) a b ∈ _`.

Rewrite using `[unipMatrix_apply]`. Use `split_ifs`. Conclude with `hyZ`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Rewrite using `[unipFin, coe_unipGL_inv]`. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => -y) a b ∈ _`. Rewrite using `[unipMatrix_apply]`. Use `split_ifs`. Conclude with `neg_mem hyZ`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `⟨mul_mem (mul_mem (inv_mem hw) hu) hw, ?_⟩` and prove the remaining obligations. Establish `hVW : ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) * (w : Matrix (Fin 2) (Fin 2) 𝔸f) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `h10 : ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 + ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = 0`. Use `congrFun (congrFun hVW 1) 0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `u00 : unipMatrix (n` using `2) (r := 1) (fun _ => y) 0 0 = 1 := by rw [unipMatrix_apply]; simp`. Establish `u01 : unipMatrix (n` using `2) (r := 1) (fun _ => y) 0 1 = y := by rw [unipMatrix_apply]; simp`.

Establish `u10 : unipMatrix (n` using `2) (r := 1) (fun _ => y) 1 0 = 0 := by rw [unipMatrix_apply]; simp`. Establish `u11 : unipMatrix (n` using `2) (r := 1) (fun _ => y) 1 1 = 1 := by rw [unipMatrix_apply]; simp`. Establish `key : ((w⁻¹ * unipFin y * w : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0) * y`. Rewrite using `[Units.val_mul, Units.val_mul]`. Express the relevant statement in the definitionally equal form `(((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) * unipMatrix (n := 2) (r := 1) (fun _ => y) * (w : Matrix (Fin 2) (Fin 2) 𝔸f)) 1 0 = _`.

Rewrite using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two, u00, u01, u10, u11]`. Take the linear combination `h10`. Rewrite using `[key]`. Use `mul_mem_levelIdeal ?_ hy` and prove the remaining obligations. Establish `h1` using `((mem_integralFiniteGL_iff ℚ 2).1 hw)`.

Conclude with `mul_mem (h1.2 1 0) (h1.1 1 0)`.
-/
theorem conj_unipFin_mem {w : FiniteAdelicGL ℚ 2} (hw : w ∈ integralFiniteGL ℚ 2) {y : 𝔸f}
    (hy : y ∈ levelIdeal N) : w⁻¹ * unipFin y * w ∈ Gamma0Level N := by
  have hyZ : y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := levelIdeal_subset N hy
  have hu : unipFin y ∈ integralFiniteGL ℚ 2 := by
    rw [mem_integralFiniteGL_iff]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change unipMatrix (n := 2) (r := 1) (fun _ => y) a b ∈ _
      rw [unipMatrix_apply]
      split_ifs
      · exact hyZ
      · exact one_mem _
      · exact zero_mem _
    · rw [unipFin, coe_unipGL_inv]
      change unipMatrix (n := 2) (r := 1) (fun _ => -y) a b ∈ _
      rw [unipMatrix_apply]
      split_ifs
      · exact neg_mem hyZ
      · exact one_mem _
      · exact zero_mem _
  refine ⟨mul_mem (mul_mem (inv_mem hw) hu) hw, ?_⟩
  have hVW : ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) * (w : Matrix (Fin 2) (Fin 2) 𝔸f) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h10 : ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 0 0 +
      ((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 = 0 := by
    have := congrFun (congrFun hVW 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have u00 : unipMatrix (n := 2) (r := 1) (fun _ => y) 0 0 = 1 := by rw [unipMatrix_apply]; simp
  have u01 : unipMatrix (n := 2) (r := 1) (fun _ => y) 0 1 = y := by rw [unipMatrix_apply]; simp
  have u10 : unipMatrix (n := 2) (r := 1) (fun _ => y) 1 0 = 0 := by rw [unipMatrix_apply]; simp
  have u11 : unipMatrix (n := 2) (r := 1) (fun _ => y) 1 1 = 1 := by rw [unipMatrix_apply]; simp
  have key : ((w⁻¹ * unipFin y * w : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 =
      (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0) * y := by
    rw [Units.val_mul, Units.val_mul]
    change (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) *
      unipMatrix (n := 2) (r := 1) (fun _ => y) * (w : Matrix (Fin 2) (Fin 2) 𝔸f)) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
      Fin.sum_univ_two, u00, u01, u10, u11]
    linear_combination h10
  rw [key]
  refine mul_mem_levelIdeal ?_ hy
  have h1 := ((mem_integralFiniteGL_iff ℚ 2).1 hw)
  exact mul_mem (h1.2 1 0) (h1.1 1 0)

/- English proof (translation)
Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Simplify using `only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`.
-/
theorem realEmb_finEmb_mul (a c : GL (Fin 2) ℝ) (b d : FiniteAdelicGL ℚ 2) :
    realEmb a * finEmb ℚ 2 b * (realEmb c * finEmb ℚ 2 d) = realEmb (a * c) * finEmb ℚ 2 (b * d) := by
  apply (prodEquiv ℚ 2).injective
  simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]

instance isAddHaarMeasure_map_realHomeomorph :
    ((infiniteAdeleMeasure ℚ).map realHomeomorph).IsAddHaarMeasure :=
  RationalIdeles.realEquiv.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure ℚ)
    RationalIdeles.continuous_realEquiv RationalIdeles.continuous_realEquiv_symm

/- English proof (translation)
The claim follows from `Measure.isAddLeftInvariant_eq_smul _ _`.
-/
theorem map_infiniteAdeleMeasure :
    (infiniteAdeleMeasure ℚ).map realHomeomorph =
      Measure.addHaarScalarFactor ((infiniteAdeleMeasure ℚ).map realHomeomorph) volume • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

/- English proof (translation)
The claim follows from `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _`.
-/
theorem addHaarScalarFactor_pos :
    0 < Measure.addHaarScalarFactor ((infiniteAdeleMeasure ℚ).map realHomeomorph) volume :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

def levelConstant : ℝ :=
  (finiteAdeleMeasure ℚ (levelIdeal N)).toReal *
    Measure.addHaarScalarFactor ((infiniteAdeleMeasure ℚ).map realHomeomorph) volume

/- English proof (translation)
Use `mul_pos (ENNReal.toReal_pos ?_ ?_) (by exact_mod_cast addHaarScalarFactor_pos)` and prove the remaining obligations. Conclude with `((isOpen_levelIdeal N).measure_pos _ ⟨0, zero_mem_levelIdeal N⟩).ne'`. Conclude with `(measure_mono (levelIdeal_subset N)).trans_lt (isCompact_integralFiniteAdeles ℚ).measure_lt_top |>.ne`.
-/
theorem levelConstant_pos : 0 < levelConstant N := by
  refine mul_pos (ENNReal.toReal_pos ?_ ?_) (by exact_mod_cast addHaarScalarFactor_pos)
  · exact ((isOpen_levelIdeal N).measure_pos _ ⟨0, zero_mem_levelIdeal N⟩).ne'
  · exact (measure_mono (levelIdeal_subset N)).trans_lt
      (isCompact_integralFiniteAdeles ℚ).measure_lt_top |>.ne

variable {N} {k : ℤ}

/- English proof (translation)
Use `set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h) * finEmb ℚ 2 w)`. Rewrite using `[constantTerm_eq_setIntegral_adele hφ.isLeftInvariant (isAddFundamentalDomain_levelDomain N)]`. Establish `heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (unipAdele x * (realEmb h * finEmb ℚ 2 w))) (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain N)`. Introduce `x hx`. Establish `e : unipAdele x * (realEmb h * finEmb ℚ 2 w) = realEmb (unipReal (RationalIdeles.realEquiv x.1) * h) * finEmb ℚ 2 w * finEmb ℚ 2 (w⁻¹ * unipFin x.2 * w)`.

Rewrite using `[unipAdele_eq]`. Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Simplify using `only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Rewrite using `[Prod.mk.injEq]`. Conclude with `⟨rfl, by group⟩`.

Simplify using `only [G]`. Rewrite using `[e, hφ.right_level _ _ (conj_unipFin_mem hw hx.2)]`. Rewrite using `[setIntegral_congr_fun (measurableSet_levelDomain N) heq]`. Use `set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) N`. Combine the equalities or inequalities in the displayed calculation.

Establish `hf` using `integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A) (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal N)) (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))`. Rewrite using `[← Measure.prod_restrict]`. Use `hf.trans ?_` and prove the remaining obligations. Rewrite using `[measureReal_restrict_apply_univ, measureReal_def]`. Use `_ = (finiteAdeleMeasure ℚ (levelIdeal N)).toReal • ∫ t in Set.Ico (0 : ℝ) N, G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by`.

Use `congr 1`. Conclude with `(realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ) G (Set.Ico (0 : ℝ) N)).symm`. Use `_ = levelConstant N • ∫ t in (0 : ℝ)..N, G t := by`. Rewrite using `[map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure, intervalIntegral.integral_of_le (Nat.cast_nonneg N), integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]`.
-/
theorem constantTerm_realEmb_mul_finEmb {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (h : GL (Fin 2) ℝ) {w : FiniteAdelicGL ℚ 2} (hw : w ∈ integralFiniteGL ℚ 2) :
    constantTerm 1 φ (realEmb h * finEmb ℚ 2 w) =
      levelConstant N • ∫ t in (0 : ℝ)..N, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) := by
  set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h) * finEmb ℚ 2 w)
  rw [constantTerm_eq_setIntegral_adele hφ.isLeftInvariant (isAddFundamentalDomain_levelDomain N)]
  have heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)))
      (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain N) := by
    intro x hx
    have e : unipAdele x * (realEmb h * finEmb ℚ 2 w) =
        realEmb (unipReal (RationalIdeles.realEquiv x.1) * h) * finEmb ℚ 2 w *
          finEmb ℚ 2 (w⁻¹ * unipFin x.2 * w) := by
      rw [unipAdele_eq]
      apply (prodEquiv ℚ 2).injective
      simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
      rw [Prod.mk.injEq]
      exact ⟨rfl, by group⟩
    simp only [G]
    rw [e, hφ.right_level _ _ (conj_unipFin_mem hw hx.2)]
  rw [setIntegral_congr_fun (measurableSet_levelDomain N) heq]
  set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) N
  calc ∫ x in levelDomain N, G (RationalIdeles.realEquiv x.1) ∂adeleMeasure ℚ
      = ∫ x in (A ×ˢ levelIdeal N : Set (InfiniteAdeleRing ℚ × 𝔸f)), G (RationalIdeles.realEquiv x.1)
          ∂((infiniteAdeleMeasure ℚ).prod (finiteAdeleMeasure ℚ)) := rfl
    _ = (finiteAdeleMeasure ℚ (levelIdeal N)).toReal •
          ∫ x in A, G (RationalIdeles.realEquiv x) ∂infiniteAdeleMeasure ℚ := by
        have hf := integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A)
          (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal N))
          (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))
        rw [← Measure.prod_restrict]
        refine hf.trans ?_
        rw [measureReal_restrict_apply_univ, measureReal_def]
    _ = (finiteAdeleMeasure ℚ (levelIdeal N)).toReal •
          ∫ t in Set.Ico (0 : ℝ) N, G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by
        congr 1
        exact (realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ)
          G (Set.Ico (0 : ℝ) N)).symm
    _ = levelConstant N • ∫ t in (0 : ℝ)..N, G t := by
        rw [map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
          intervalIntegral.integral_of_le (Nat.cast_nonneg N), integral_Ico_eq_integral_Ioo,
          ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]

end GL2Classical

end

end GroundTheory.Automorphic
