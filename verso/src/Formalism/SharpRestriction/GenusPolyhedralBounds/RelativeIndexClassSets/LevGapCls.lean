import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.UG.P
open scoped TensorProduct

section Abstract

variable {G : Type} [Group G]

/- English proof (translation)
Establish `hfi : (U.subgroupOf K).FiniteIndex` using `⟨h⟩`. Establish `hq : Finite (K ⧸ U.subgroupOf K)` using `inferInstance`. Set `ψ : ClassSet Γ K × (K ⧸ U.subgroupOf K) → ClassSet Γ U` to `fun p => DoubleCoset.mk _ _ (p.1.out * ((p.2.out : K) : G))`. Use `Finite.of_surjective ψ ?_` and prove the remaining obligations. Introduce `q`.

Take `⟨g, rfl⟩` from `Quotient.exists_rep q`. Take `⟨a, b, ha, hb, hab⟩` from `DoubleCoset.mk_out_eq_mul Γ K g`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨b, hb⟩⁻¹ : K)`. Use `⟨(DoubleCoset.mk Γ K g, ((⟨b, hb⟩⁻¹ : K) : K ⧸ U.subgroupOf K)), ?_⟩` and prove the remaining obligations. Use `show DoubleCoset.mk Γ U _ = DoubleCoset.mk Γ U g`.

Rewrite using `[eq_comm, DoubleCoset.eq]`. Use `⟨a, ha, ((u : K) : G), Subgroup.mem_subgroupOf.1 u.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hab, hu]`. Simplify using `[mul_assoc]`.
-/
theorem classSet_finite_of_relIndex (Γ K U : Subgroup G) (h : U.relIndex K ≠ 0)
    (hK : Finite (ClassSet Γ K)) : Finite (ClassSet Γ U) := by
  have hfi : (U.subgroupOf K).FiniteIndex := ⟨h⟩
  have hq : Finite (K ⧸ U.subgroupOf K) := inferInstance
  let ψ : ClassSet Γ K × (K ⧸ U.subgroupOf K) → ClassSet Γ U :=
    fun p => DoubleCoset.mk _ _ (p.1.out * ((p.2.out : K) : G))
  refine Finite.of_surjective ψ ?_
  intro q
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨b, hb⟩⁻¹ : K)
  refine ⟨(DoubleCoset.mk Γ K g, ((⟨b, hb⟩⁻¹ : K) : K ⧸ U.subgroupOf K)), ?_⟩
  show DoubleCoset.mk Γ U _ = DoubleCoset.mk Γ U g
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨a, ha, ((u : K) : G), Subgroup.mem_subgroupOf.1 u.2, ?_⟩
  rw [hab, hu]
  simp [mul_assoc]

end Abstract

section Princ

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `h1` using `congrArg (fun u : GL n (R ⧸ I) => (u : Matrix n n (R ⧸ I)) i j) h`. Establish `h2 : Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j` using `h1`. Rewrite using `[← Ideal.Quotient.eq, h2, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `h`. Use extensionality with `i j`. Use `show Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j`. Rewrite using `[Ideal.Quotient.eq.2 (h i j), Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem cls_redGL_eq_one_iff {R : Type} [CommRing R] (I : Ideal R) (g : GL n R) :
    redGL I g = 1 ↔ ∀ i j, (g : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  constructor
  · intro h i j
    have h1 := congrArg (fun u : GL n (R ⧸ I) => (u : Matrix n n (R ⧸ I)) i j) h
    have h2 : Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j := h1
    rw [← Ideal.Quotient.eq, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    show Ideal.Quotient.mk I ((g : Matrix n n R) i j) = (1 : Matrix n n (R ⧸ I)) i j
    rw [Ideal.Quotient.eq.2 (h i j), Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Unfold `princ congPre`. Rewrite using `[Subgroup.mem_map]`. Simplify using `only [Subgroup.mem_comap, Subgroup.mem_bot, cls_redGL_eq_one_iff]`.
-/
theorem cls_mem_princ_iff {A R : Type} [CommRing A] [CommRing R] (ι : R →+* A) (I : Ideal R) (g : GL n A) :
    g ∈ princ (n := n) ι I ↔ ∃ g0 : GL n R, (∀ i j, (g0 : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I) ∧
      bc ι g0 = g := by
  unfold princ congPre
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_comap, Subgroup.mem_bot, cls_redGL_eq_one_iff]

/- English proof (translation)
Rewrite `hg`, the goal using `[cls_mem_princ_iff]`. Take `⟨g0, h0, rfl⟩` from `hg`. Use `⟨bc ψ0 g0, fun i j => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hI (h0 i j)`. Rewrite `h1` using `[Ideal.mem_comap, map_sub]`.

Establish `h2 : ψ0 ((1 : Matrix n n R) i j) = (1 : Matrix n n R') i j`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite `h1` using `[h2]`. Conclude with `h1`. Use extensionality with `i j`.

Conclude with `hψ _`.
-/
theorem cls_princ_map {A R A' R' : Type} [CommRing A] [CommRing R] [CommRing A'] [CommRing R']
    (ι : R →+* A) (I : Ideal R) (ι' : R' →+* A') (I' : Ideal R') (ψ : A →+* A') (ψ0 : R →+* R')
    (hψ : ∀ x, ι' (ψ0 x) = ψ (ι x)) (hI : I ≤ I'.comap ψ0) (g : GL n A) (hg : g ∈ princ (n := n) ι I) :
    bc ψ g ∈ princ (n := n) ι' I' := by
  rw [cls_mem_princ_iff] at hg ⊢
  obtain ⟨g0, h0, rfl⟩ := hg
  refine ⟨bc ψ0 g0, fun i j => ?_, ?_⟩
  · have h1 := hI (h0 i j)
    rw [Ideal.mem_comap, map_sub] at h1
    have h2 : ψ0 ((1 : Matrix n n R) i j) = (1 : Matrix n n R') i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h2] at h1
    exact h1
  · ext i j
    exact hψ _

/- English proof (translation)
The claim follows from `Subgroup.map_mono (Subgroup.comap_mono bot_le)`.
-/
theorem cls_princ_le_congPre {A R : Type} [CommRing A] [CommRing R] (ι : R →+* A) (I : Ideal R)
    (H : Subgroup (GL n (R ⧸ I))) : princ (n := n) ι I ≤ congPre ι I H :=
  Subgroup.map_mono (Subgroup.comap_mono bot_le)

variable {L : Type} [CommRing L]

/- English proof (translation)
Rewrite `hg` using `[cls_mem_princ_iff]`. Take `⟨g0, h0, rfl⟩` from `hg`. Establish `h2 : ∀ i j, ∃ b : O, (g0 : Matrix n n O) i j - (1 : Matrix n n O) i j = b * (t * c')` using `fun i j => by`. Use `hI (h0 i j)` as an intermediate fact. Rewrite `this` using `[Ideal.mem_span_singleton']`.

Take `⟨b, hb⟩` from `this`. Conclude with `⟨b, hb.symm⟩`. Use `choose b hb using h2`. Introduce `x hx`. Use `⟨fun i => ∑ j, (b i j : L) * ((t : L) * x j), fun i => Subring.sum_mem _ fun j _ => mul_mem (b i j).2 (h1 x hx j), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `h3 : ∀ j, ((bc (n` using `n) O.subtype g0 : GL n L) : Matrix n n L) i j = (1 : Matrix n n L) i j + (b i j : L) * ((t : L) * (c' : L)) := by`. Introduce `j`. Establish `h4` using `congrArg (fun z : O => (z : L)) (hb i j)`. Simplify using `only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h4`.

Establish `h5 : (((1 : Matrix n n O) i j : O) : L) = (1 : Matrix n n L) i j`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite `h4` using `[h5]`. Use `show (((g0 : Matrix n n O) i j : O) : L) = _`. Rewrite using `[← h4]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.mulVec, dotProduct, h3, add_mul, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`. Rewrite using `[Subring.smul_def, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cls_princ_move (O : Subring L) (I : Ideal O) (t c' : O) (hI : I ≤ Ideal.span {t * c'}) (M : Submodule O (n → L))
    (h1 : ∀ x ∈ M, ∀ i, (t : L) * x i ∈ O) (g : GL n L) (hg : g ∈ princ (n := n) O.subtype I) :
    ∀ x ∈ M, ∃ y : n → L, (∀ i, y i ∈ O) ∧ (g : Matrix n n L) *ᵥ x = x + c' • y := by
  rw [cls_mem_princ_iff] at hg
  obtain ⟨g0, h0, rfl⟩ := hg
  have h2 : ∀ i j, ∃ b : O, (g0 : Matrix n n O) i j - (1 : Matrix n n O) i j = b * (t * c') := fun i j => by
    have := hI (h0 i j)
    rw [Ideal.mem_span_singleton'] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.symm⟩
  choose b hb using h2
  intro x hx
  refine ⟨fun i => ∑ j, (b i j : L) * ((t : L) * x j), fun i => Subring.sum_mem _ fun j _ => mul_mem (b i j).2 (h1 x hx j), ?_⟩
  funext i
  have h3 : ∀ j, ((bc (n := n) O.subtype g0 : GL n L) : Matrix n n L) i j =
      (1 : Matrix n n L) i j + (b i j : L) * ((t : L) * (c' : L)) := by
    intro j
    have h4 := congrArg (fun z : O => (z : L)) (hb i j)
    simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h4
    have h5 : (((1 : Matrix n n O) i j : O) : L) = (1 : Matrix n n L) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h5] at h4
    show (((g0 : Matrix n n O) i j : O) : L) = _
    rw [← h4]; ring
  simp only [Matrix.mulVec, dotProduct, h3, add_mul, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply]
  congr 1
  · simp [Matrix.one_apply]
  · rw [Subring.smul_def, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Establish `key : ∀ g : GL n L, g ∈ princ (n` using `n) O.subtype I → ∀ x ∈ M, (g : Matrix n n L) *ᵥ x ∈ M := by`. Introduce `g hg x hx`. Take `⟨y, hy, hxy⟩` from `cls_princ_move O I t c' hI M h1 g hg x hx`. Rewrite using `[hxy]`. Conclude with `add_mem hx (h2 y hy)`.

Introduce `x`. Use `⟨key g hg x, fun hx => ?_⟩` and prove the remaining obligations. Use `key g⁻¹ (inv_mem hg) _ hx` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem cls_princ_stab (O : Subring L) (I : Ideal O) (t c' : O) (hI : I ≤ Ideal.span {t * c'}) (M : Submodule O (n → L))
    (h1 : ∀ x ∈ M, ∀ i, (t : L) * x i ∈ O) (h2 : ∀ y : n → L, (∀ i, y i ∈ O) → c' • y ∈ M)
    (g : GL n L) (hg : g ∈ princ (n := n) O.subtype I) : g ∈ stabGL M := by
  have key : ∀ g : GL n L, g ∈ princ (n := n) O.subtype I → ∀ x ∈ M, (g : Matrix n n L) *ᵥ x ∈ M := by
    intro g hg x hx
    obtain ⟨y, hy, hxy⟩ := cls_princ_move O I t c' hI M h1 g hg x hx
    rw [hxy]
    exact add_mem hx (h2 y hy)
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Princ

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

/- English proof (translation)
Introduce `x hx i`. Unfold `latS at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`.

Take `⟨e, he⟩` from `h l hl i`. Establish `h1 : (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F` using `F) (v.adicCompletion F) (l i) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E e) := by`. Rewrite using `[he, map_mul, map_natCast]`. Both sides reduce to the same expression. Use `show (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (l i) ∈ _`.

Rewrite using `[h1]`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)`. Consider the case `zero => rw [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, mul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]`. Conclude with `mul_mem a.2 hx`.
-/
theorem cls_latS_entries (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin k → E)) (t : ℕ)
    (h : ∀ x ∈ Λ, ∀ i, (t : E) * x i ∈ intOE E) :
    ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ, ∀ i,
      (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * x i ∈ intV E v := by
  intro x hx i
  unfold latS at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨e, he⟩ := h l hl i
    have h1 : (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (l i) =
        inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E e) := by
      rw [he, map_mul, map_natCast]; rfl
    show (((t : ℕ) : intV E v) : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (l i) ∈ _
    rw [h1]
    exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)
  | zero => rw [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem a.2 hx

/- English proof (translation)
Establish `h1 : ((c : ℕ) : intV E v) • y = ∑ i, (⟨y i, hy i⟩ : intV E v) • (fun j => inclE (F` using `F) (v.adicCompletion F) (((c : E) • (Pi.single i 1 : Fin k → E)) j)) := by`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`. Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one, map_natCast]`. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Introduce `b _ hb`. Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne hb.symm, mul_zero, map_zero]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.

Rewrite using `[h1]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h i, rfl⟩)`.
-/
theorem cls_latS_contains (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin k → E)) (c : ℕ)
    (h : ∀ i, (c : E) • (Pi.single i 1 : Fin k → E) ∈ Λ) (y : Fin k → E ⊗[F] v.adicCompletion F)
    (hy : ∀ i, y i ∈ intV E v) :
    ((c : ℕ) : intV E v) • y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  have h1 : ((c : ℕ) : intV E v) • y = ∑ i, (⟨y i, hy i⟩ : intV E v) •
      (fun j => inclE (F := F) (v.adicCompletion F) (((c : E) • (Pi.single i 1 : Fin k → E)) j)) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one, map_natCast]
      rw [mul_comm]; rfl
    · intro b _ hb
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne hb.symm, mul_zero, map_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h i, rfl⟩)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem cls_latS_mono (v : HeightOneSpectrum (𝓞 F)) {Λ Λ' : Submodule (𝓞 E) (Fin k → E)} (h : Λ ≤ Λ') :
    latS (F := F) (v.adicCompletion F) (intV E v) Λ ≤ latS (F := F) (v.adicCompletion F) (intV E v) Λ' :=
  Submodule.span_mono (Set.image_mono h)

namespace Par

variable (P : Par F E k)

def clsD : ℕ := P.T * P.T * (P.gp 0 * P.gp 1)

/- English proof (translation)
Unfold `Par.Lb LbOf at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Unfold `lbVec`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `⟨P.pz, rfl⟩`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem ⟨a, rfl⟩ hx`.
-/
theorem cls_Lb_entries (x : Fin k → E) (hx : x ∈ P.Lb) (i : Fin k) : x i ∈ intOE E := by
  unfold Par.Lb LbOf at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    unfold lbVec
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨P.pz, rfl⟩
    · exact one_mem _
    · exact zero_mem _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ hx

/- English proof (translation)
Take `⟨z, hz⟩` from `hz`. Establish `hz' : (z : E) * (P.pz : E) = (P.T : E)`. Use `congrArg (algebraMap (𝓞 E) E) hz` as an intermediate fact. Simplify using `using this`. Establish `h1 : (P.T : E) • (Pi.single i 1 : Fin k → E) = (if i.1 = 0 then z else (P.T : 𝓞 E)) • lbVec k P.pz i`.

Use function extensionality and compare the values at `j`. Unfold `lbVec`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]`.

Use `split_ifs`. Conclude with `hz'.symm`. Simplify using the standard rewrite rules. Simplify using `only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]`. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem cls_T_single (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E)) (i : Fin k) :
    (P.T : E) • (Pi.single i 1 : Fin k → E) ∈ P.Lb := by
  obtain ⟨z, hz⟩ := hz
  have hz' : (z : E) * (P.pz : E) = (P.T : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hz
    simpa using this
  have h1 : (P.T : E) • (Pi.single i 1 : Fin k → E) =
      (if i.1 = 0 then z else (P.T : 𝓞 E)) • lbVec k P.pz i := by
    funext j
    unfold lbVec
    by_cases hj : j = i
    · subst hj
      simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      split_ifs
      · exact hz'.symm
      · simp
    · simp only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E))
  (hint : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb)
  (hdual : ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb)

include hz in
/- English proof (translation)
Use `cls_princ_stab (intV E v) _ ((1 : ℕ) : intV E v) ((P.T : ℕ) : intV E v) ?_ (P.LbV v) (cls_latS_entries v P.Lb 1 fun x hx i => by simpa using P.cls_Lb_entries x hx i) (cls_latS_contains v P.Lb P.T (P.cls_T_single hz)) g hg` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `⟨((P.T * (P.gp 0 * P.gp 1) : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩`.
-/
theorem cls_princ_le_stabLb (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((P.clsD : ℕ) : intV E v)})) :
    g ∈ stabGL (P.LbV v) := by
  refine cls_princ_stab (intV E v) _ ((1 : ℕ) : intV E v) ((P.T : ℕ) : intV E v) ?_ (P.LbV v)
    (cls_latS_entries v P.Lb 1 fun x hx i => by simpa using P.cls_Lb_entries x hx i)
    (cls_latS_contains v P.Lb P.T (P.cls_T_single hz)) g hg
  rw [Ideal.span_singleton_le_span_singleton]
  exact ⟨((P.T * (P.gp 0 * P.gp 1) : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩

include hdual in
/- English proof (translation)
Establish `h1 : (P.T : E) • x ∈ P.Lb`. Unfold `Par.Ld at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hdual x hx`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.

Conclude with `P.cls_Lb_entries _ h1 i`.
-/
theorem cls_Ld_entries (x : Fin k → E) (hx : x ∈ P.Ld) (i : Fin k) : (P.T : E) * x i ∈ intOE E := by
  have h1 : (P.T : E) • x ∈ P.Lb := by
    unfold Par.Ld at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hdual x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  exact P.cls_Lb_entries _ h1 i

include hz hint hdual in
/- English proof (translation)
Establish `hI : Ideal.span {((P.clsD : ℕ) : intV E v)} ≤ Ideal.span {((P.T : ℕ) : intV E v) * ((P.T : ℕ) : intV E v)}`. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `⟨((P.gp 0 * P.gp 1 : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩`. Establish `hle : P.Lb ≤ P.Ld` using `fun x hx => Submodule.subset_span (hint x hx)`. Establish `hst : g ∈ stabGL (P.LdV v)` using `cls_princ_stab (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v) (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual)) (fun y hy => cls_latS_mono v hle (cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy)) g hg`.

Use `⟨hst, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `cls_princ_move (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v) (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual)) g hg x.1 x.2`. Unfold `Par.fT`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `Submodule.mem_sup_left ?_` and prove the remaining obligations.

Rewrite using `[Submodule.mem_comap]`. Use `show (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ x.1 - x.1 ∈ P.LbV v`. Rewrite using `[hxy, add_sub_cancel_left]`. Conclude with `cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy`.
-/
theorem cls_princ_le_stabFun (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((P.clsD : ℕ) : intV E v)})) :
    g ∈ stabFun (P.LdV v) (P.fT v) := by
  have hI : Ideal.span {((P.clsD : ℕ) : intV E v)} ≤
      Ideal.span {((P.T : ℕ) : intV E v) * ((P.T : ℕ) : intV E v)} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact ⟨((P.gp 0 * P.gp 1 : ℕ) : intV E v), by unfold Par.clsD; push_cast; ring⟩
  have hle : P.Lb ≤ P.Ld := fun x hx => Submodule.subset_span (hint x hx)
  have hst : g ∈ stabGL (P.LdV v) :=
    cls_princ_stab (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v)
      (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual))
      (fun y hy => cls_latS_mono v hle (cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy)) g hg
  refine ⟨hst, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := cls_princ_move (intV E v) _ ((P.T : ℕ) : intV E v) ((P.T : ℕ) : intV E v) hI (P.LdV v)
      (cls_latS_entries v P.Ld P.T (P.cls_Ld_entries hdual)) g hg x.1 x.2
  unfold Par.fT
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine Submodule.mem_sup_left ?_
  rw [Submodule.mem_comap]
  show (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ x.1 - x.1 ∈ P.LbV v
  rw [hxy, add_sub_cancel_left]
  exact cls_latS_contains v P.Lb P.T (P.cls_T_single hz) y hy

/- English proof (translation)
Establish `h1 : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (m : 𝓞 F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Use `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).2 ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.adicCompletion.valued_coe (K := F) (v := v), HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 hm`. Rewrite `h1` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem cls_natCast_mem_max (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : (m : 𝓞 F) ∈ v.asIdeal) :
    (m : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  have h1 : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (m : 𝓞 F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).2 ?_
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.adicCompletion.valued_coe (K := F) (v := v), HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 hm
  rwa [map_natCast] at h1

/- English proof (translation)
Unfold `Par.clsD`. Use `fin_cases i`. Conclude with `⟨P.T * P.T * P.gp 1, by simp only [Fin.zero_eta]; ring⟩`. Conclude with `⟨P.T * P.T * P.gp 0, by simp only [Fin.mk_one]; ring⟩`.
-/
theorem cls_gp_dvd (i : Fin 2) : P.gp i ∣ P.clsD := by
  unfold Par.clsD
  fin_cases i
  · exact ⟨P.T * P.T * P.gp 1, by simp only [Fin.zero_eta]; ring⟩
  · exact ⟨P.T * P.T * P.gp 0, by simp only [Fin.mk_one]; ring⟩

/- English proof (translation)
Apply `cls_princ_le_congPre` to reduce the goal to its premises. Set `ψ0 : intV E v →+* v.adicCompletionIntegers F` to `(((RingHom.fst _ _).comp s.φ.toRingHom).comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) (fun x => ((s.int x).1 x.2).1)`. Use `cls_princ_map (intV E v).subtype _ (algebraMap _ _) _ _ ψ0 (fun x => rfl) ?_ g hg` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Take `⟨r, hr⟩` from `P.cls_gp_dvd i`.

Rewrite using `[hr, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (cls_natCast_mem_max v _ hv)`.
-/
theorem cls_princ_le_iw (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (P.gp i : 𝓞 F) ∈ v.asIdeal)
    (s : SplitAt P.σ v (P.a i)) (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((P.clsD : ℕ) : intV E v)})) :
    bc ((RingHom.fst _ _).comp s.φ.toRingHom) g ∈ iwU F k v := by
  apply cls_princ_le_congPre
  let ψ0 : intV E v →+* v.adicCompletionIntegers F :=
    (((RingHom.fst _ _).comp s.φ.toRingHom).comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F)
      (fun x => ((s.int x).1 x.2).1)
  refine cls_princ_map (intV E v).subtype _ (algebraMap _ _) _ _ ψ0 (fun x => rfl) ?_ g hg
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  obtain ⟨r, hr⟩ := P.cls_gp_dvd i
  rw [hr, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (cls_natCast_mem_max v _ hv)

end Par

end Loc

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

namespace Par

variable (P : Par F E k)

/- English proof (translation)
Set `ψ0 : 𝒮 →+* intV E v` to `((prV (E := E) v).comp (𝒮).subtype).codRestrict (intV E v) (fun x => afsplit_prV_int (E := E) v (x : 𝒜) x.2)`. Use `cls_princ_map (𝒮).subtype _ (intV E v).subtype _ _ ψ0 (fun x => rfl) ?_ g hg` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem cls_princ_prV (m : ℕ) (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin k) 𝒜)
    (hg : g ∈ princ (n := Fin k) (𝒮).subtype (Ideal.span {((m : ℕ) : 𝒮)})) :
    bc (prV (E := E) v) g ∈ princ (n := Fin k) (intV E v).subtype (Ideal.span {((m : ℕ) : intV E v)}) := by
  let ψ0 : 𝒮 →+* intV E v :=
    ((prV (E := E) v).comp (𝒮).subtype).codRestrict (intV E v) (fun x => afsplit_prV_int (E := E) v (x : 𝒜) x.2)
  refine cls_princ_map (𝒮).subtype _ (intV E v).subtype _ _ ψ0 (fun x => rfl) ?_ g hg
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/- English proof (translation)
Use `Subgroup.mem_inf.2 ⟨hU, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_iInf]`. Introduce `v`. Rewrite using `[Subgroup.mem_comap]`. Establish `h1 : bc (prV (E` using `E) v) g ∈ UPts P.σ P.J (v.adicCompletion F) := afsplit_bc_mem P.σ P.J v g hU`.

Establish `h2` using `cls_princ_prV (E := E) P.clsD v g hg`. Establish `h3 : bc (prV (E` using `E) v) g ∈ levelVL P.σ P.J v P.Lb := Subgroup.mem_inf.2 ⟨h1, P.cls_princ_le_stabLb hz v _ h2⟩`. Unfold `Par.Uloc`. Use `split_ifs with hT h0 h1'`. Conclude with `Subgroup.mem_inf.2 ⟨h3, P.cls_princ_le_stabFun hz hint hdual v _ h2⟩`.

Conclude with `Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_comap.2 (P.cls_princ_le_iw 0 v h0 _ _ h2)⟩`. Conclude with `Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_comap.2 (P.cls_princ_le_iw 1 v h1' _ _ h2)⟩`. Conclude with `h3`.
-/
theorem cls_princ_le_U (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E))
    (hint : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb)
    (hdual : ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb)
    (S : P.Splits) (g : GL (Fin k) 𝒜) (hU : g ∈ P.GA)
    (hg : g ∈ princ (n := Fin k) (𝒮).subtype (Ideal.span {((P.clsD : ℕ) : 𝒮)})) : g ∈ P.U S := by
  refine Subgroup.mem_inf.2 ⟨hU, ?_⟩
  rw [Subgroup.mem_iInf]
  intro v
  rw [Subgroup.mem_comap]
  have h1 : bc (prV (E := E) v) g ∈ UPts P.σ P.J (v.adicCompletion F) := afsplit_bc_mem P.σ P.J v g hU
  have h2 := cls_princ_prV (E := E) P.clsD v g hg
  have h3 : bc (prV (E := E) v) g ∈ levelVL P.σ P.J v P.Lb :=
    Subgroup.mem_inf.2 ⟨h1, P.cls_princ_le_stabLb hz v _ h2⟩
  unfold Par.Uloc
  split_ifs with hT h0 h1'
  · exact Subgroup.mem_inf.2 ⟨h3, P.cls_princ_le_stabFun hz hint hdual v _ h2⟩
  · exact Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_comap.2 (P.cls_princ_le_iw 0 v h0 _ _ h2)⟩
  · exact Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_comap.2 (P.cls_princ_le_iw 1 v h1' _ _ h2)⟩
  · exact h3

/- English proof (translation)
Introduce `S`. Establish `hD : P.clsD ≠ 0` using `mul_ne_zero (mul_ne_zero hT hT) (mul_ne_zero (hgp 0) (hgp 1))`. Establish `hc : ((((P.clsD : ℕ) : 𝒮) : 𝒮) : 𝒜) = levelafC E ((P.clsD : ℕ) : 𝓞 F)`. Unfold `levelafC`. Rewrite using `[map_natCast, ← Algebra.TensorProduct.natCast_def']`.

Both sides reduce to the same expression. Establish `hfin : Finite (𝒮 ⧸ Ideal.span {((P.clsD : ℕ) : 𝒮)})` using `levelaf_finite_quot ((P.clsD : ℕ) : 𝓞 F) (Nat.cast_ne_zero.2 hD) _ hc`. Establish `hne` using `levelaf_princ_relIndex_ne_zero (n := Fin k) (𝒮) (Ideal.span {((P.clsD : ℕ) : 𝒮)})`. Establish `hstab : stabGL (stdLat (n` using `Fin k) (A := 𝒜) (𝒮)) = (bc (n := Fin k) (𝒮).subtype).range := stabilizer_standard_lattice _ _ (Fin k) Subtype.val_injective`. Establish `hLU : levelAf P.σ P.J ≤ P.GA` using `inf_le_left`.

Establish `hLS : levelAf P.σ P.J ≤ (bc (n` using `Fin k) (𝒮).subtype).range := hstab ▸ inf_le_right`. Establish `h1 : (princ (n` using `Fin k) (𝒮).subtype (Ideal.span {((P.clsD : ℕ) : 𝒮)})).subgroupOf P.GA ≤ (P.U S).subgroupOf P.GA := by`. Introduce `h hh`. Rewrite `hh`, the goal using `[Subgroup.mem_subgroupOf]`. Conclude with `P.cls_princ_le_U hz hint hdual S _ h.2 hh`.

Establish `h2 : ((princ (n` using `Fin k) (𝒮).subtype (Ideal.span {((P.clsD : ℕ) : 𝒮)})).subgroupOf P.GA).relIndex ((levelAf P.σ P.J).subgroupOf P.GA) ≠ 0 := by`. Rewrite using `[Subgroup.relIndex_subgroupOf hLU]`. Introduce `h0`. Conclude with `hne (Subgroup.relIndex_eq_zero_of_le_right hLS h0)`. Establish `h3 : ((P.U S).subgroupOf P.GA).relIndex ((levelAf P.σ P.J).subgroupOf P.GA) ≠ 0`.

Introduce `h0`. Establish `hd` using `Subgroup.relIndex_dvd_of_le_left ((levelAf P.σ P.J).subgroupOf P.GA) h1`. Rewrite `hd` using `[h0]`. Conclude with `h2 (Nat.eq_zero_of_zero_dvd hd)`. Conclude with `classSet_finite_of_relIndex _ _ _ h3 (lattice_class_set_finite_holds F E (Fin k) P.σ P.J hσ hJ hdet hdef)`.
-/
theorem clsFinite_of (hσ : ∀ τ : E →+* ℂ, τ.comp (P.σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hJ : IsHerm (P.σ : E →+* E) P.J) (hdet : IsUnit P.J.det) (hdef : IsTotDef P.σ P.J)
    (hT : P.T ≠ 0) (hgp : ∀ i, P.gp i ≠ 0)
    (hz : ∃ z : 𝓞 E, z * P.pz = (P.T : 𝓞 E))
    (hint : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb)
    (hdual : ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb) : P.ClsFinite := by
  intro S
  have hD : P.clsD ≠ 0 := mul_ne_zero (mul_ne_zero hT hT) (mul_ne_zero (hgp 0) (hgp 1))
  have hc : ((((P.clsD : ℕ) : 𝒮) : 𝒮) : 𝒜) = levelafC E ((P.clsD : ℕ) : 𝓞 F) := by
    unfold levelafC
    rw [map_natCast, ← Algebra.TensorProduct.natCast_def']
    rfl
  have hfin : Finite (𝒮 ⧸ Ideal.span {((P.clsD : ℕ) : 𝒮)}) :=
    levelaf_finite_quot ((P.clsD : ℕ) : 𝓞 F) (Nat.cast_ne_zero.2 hD) _ hc
  have hne := levelaf_princ_relIndex_ne_zero (n := Fin k) (𝒮) (Ideal.span {((P.clsD : ℕ) : 𝒮)})
  have hstab : stabGL (stdLat (n := Fin k) (A := 𝒜) (𝒮)) = (bc (n := Fin k) (𝒮).subtype).range :=
    stabilizer_standard_lattice _ _ (Fin k) Subtype.val_injective
  have hLU : levelAf P.σ P.J ≤ P.GA := inf_le_left
  have hLS : levelAf P.σ P.J ≤ (bc (n := Fin k) (𝒮).subtype).range := hstab ▸ inf_le_right
  have h1 : (princ (n := Fin k) (𝒮).subtype (Ideal.span {((P.clsD : ℕ) : 𝒮)})).subgroupOf P.GA ≤
      (P.U S).subgroupOf P.GA := by
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    exact P.cls_princ_le_U hz hint hdual S _ h.2 hh
  have h2 : ((princ (n := Fin k) (𝒮).subtype (Ideal.span {((P.clsD : ℕ) : 𝒮)})).subgroupOf P.GA).relIndex
      ((levelAf P.σ P.J).subgroupOf P.GA) ≠ 0 := by
    rw [Subgroup.relIndex_subgroupOf hLU]
    intro h0
    exact hne (Subgroup.relIndex_eq_zero_of_le_right hLS h0)
  have h3 : ((P.U S).subgroupOf P.GA).relIndex ((levelAf P.σ P.J).subgroupOf P.GA) ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_of_le_left ((levelAf P.σ P.J).subgroupOf P.GA) h1
    rw [h0] at hd
    exact h2 (Nat.eq_zero_of_zero_dvd hd)
  exact classSet_finite_of_relIndex _ _ _ h3
    (lattice_class_set_finite_holds F E (Fin k) P.σ P.J hσ hJ hdet hdef)

end Par

end Glob

section Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

/- English proof (translation)
Take `⟨e, rfl⟩` from `hx`. Conclude with `⟨⟨σ (algebraMap (𝓞 E) E e), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe e)⟩, rfl⟩`.
-/
theorem cls_map_intOE (σ : E →+* E) {x : E} (hx : x ∈ intOE E) : σ x ∈ intOE E := by
  obtain ⟨e, rfl⟩ := hx
  exact ⟨⟨σ (algebraMap (𝓞 E) E e), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe e)⟩, rfl⟩

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne hj.symm]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem cls_hform_one_single (σ : E →+* E) (i : Fin k) (c : E) (y : Fin k → E) :
    hform σ 1 (Pi.single i c) y = σ c * y i := by
  unfold hform
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

namespace Par

variable (P : Par F E k)

/- English proof (translation)
Introduce `y hy x hx`. Rewrite using `[hJ]`. Use `show hform (P.σ : E →+* E) 1 x y ∈ intOE E`. Unfold `hform`. Use `Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (mul_mem (cls_map_intOE _ (P.cls_Lb_entries x hx i)) (afsplit_one_mem _ i j)) (P.cls_Lb_entries y hy j)` and prove the remaining obligations.
-/
theorem cls_int_of_std (hJ : P.J = 1) : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb := by
  intro y hy x hx
  rw [hJ]
  show hform (P.σ : E →+* E) 1 x y ∈ intOE E
  unfold hform
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    mul_mem (mul_mem (cls_map_intOE _ (P.cls_Lb_entries x hx i)) (afsplit_one_mem _ i j)) (P.cls_Lb_entries y hy j)

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[hJ]`. Establish `h1 : ∀ i : Fin k, ∃ w : 𝓞 E, (w : E) = (P.σ : E →+* E) (if i.1 = 0 then (P.pz : E) else 1) * y i`. Introduce `i`. Take `⟨w, hw⟩` from `hy (lbVec k P.pz i) (Submodule.subset_span ⟨i, rfl⟩)`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← cls_hform_one_single]`. Conclude with `hw`. Use `choose w hw using h1`. Establish `h2 : (P.T : E) • y = ∑ i, ((if i.1 = 0 then 1 else (P.T : 𝓞 E)) * w i) • lbVec k P.pz i`.

Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`. Unfold `lbVec`. Establish `e : ∀ x : E, algebraMap E E x = x` using `fun _ => rfl`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, map_mul, e]`.

Establish `hwj` using `hw j`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (w j) = _ at hwj`. Rewrite using `[hwj]`. Use `split_ifs`. Rewrite using `[← hpz, map_one] show _ = 1 * (P.σ (P.pz : E) * y j) * (P.pz : E)`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Introduce `b _ hb`. Unfold `lbVec`. Simplify using `only [Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite using `[h2]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem cls_dual_of_std (hJ : P.J = 1) (hpz : (P.pz : E) * P.σ (P.pz : E) = (P.T : E)) :
    ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb := by
  intro y hy
  rw [hJ] at hy
  have h1 : ∀ i : Fin k, ∃ w : 𝓞 E, (w : E) = (P.σ : E →+* E) (if i.1 = 0 then (P.pz : E) else 1) * y i := by
    intro i
    obtain ⟨w, hw⟩ := hy (lbVec k P.pz i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨w, ?_⟩
    rw [← cls_hform_one_single]
    exact hw
  choose w hw using h1
  have h2 : (P.T : E) • y = ∑ i, ((if i.1 = 0 then 1 else (P.T : 𝓞 E)) * w i) • lbVec k P.pz i := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · unfold lbVec
      have e : ∀ x : E, algebraMap E E x = x := fun _ => rfl
      simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, map_mul, e]
      have hwj := hw j
      change algebraMap (𝓞 E) E (w j) = _ at hwj
      rw [hwj]
      split_ifs
      · rw [← hpz, map_one]
        show _ = 1 * (P.σ (P.pz : E) * y j) * (P.pz : E)
        ring
      · simp
    · intro b _ hb
      unfold lbVec
      simp only [Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Par

end Std

/- English proof (translation)
Introduce `R H T pz piG h`. Establish `hσ : ∀ τ : H.E →+* ℂ, τ.comp (Examples₂.conjF H : H.E →+* H.E) = (starRingEnd ℂ).comp τ`. Introduce `τ`. Use extensionality with `x`. Conclude with `Examples₂.emb_conj H τ x`.

Establish `hstd` using `standard_hermitian_form_definite H.F H.E (Fin R.k) (Examples₂.conjF H) hσ (fun e he => ⟨⟨e, (Examples₂.conj_eq_self_iff H e).1 he⟩, rfl⟩) (Examples₂.cmData H).totReal`. Use `Par.clsFinite_of (hostPar H T pz piG) hσ hstd.1 (by simp [hostPar]) hstd.2.1 h.T_prime.ne_zero (fun i => (H.g_prime i).ne_zero) ?_ (Par.cls_int_of_std _ rfl) (Par.cls_dual_of_std _ rfl h.pz_norm)` and prove the remaining obligations. Use `⟨⟨H.conj (pz : H.E), map_isIntegral_int (H.conj : H.E →+* H.E) (RingOfIntegers.isIntegral_coe pz)⟩, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show H.conj (pz : H.E) * (pz : H.E) = ((T : 𝓞 H.E) : H.E)`.

Rewrite using `[mul_comm, h.pz_norm]`. Simplify using the standard rewrite rules.
-/
theorem factClsFinite : FactClsFinite := by
  intro R H T pz piG h
  have hσ : ∀ τ : H.E →+* ℂ, τ.comp (Examples₂.conjF H : H.E →+* H.E) = (starRingEnd ℂ).comp τ := by
    intro τ
    ext x
    exact Examples₂.emb_conj H τ x
  have hstd := standard_hermitian_form_definite H.F H.E (Fin R.k) (Examples₂.conjF H) hσ
    (fun e he => ⟨⟨e, (Examples₂.conj_eq_self_iff H e).1 he⟩, rfl⟩) (Examples₂.cmData H).totReal
  refine Par.clsFinite_of (hostPar H T pz piG) hσ hstd.1 (by simp [hostPar]) hstd.2.1 h.T_prime.ne_zero
    (fun i => (H.g_prime i).ne_zero) ?_ (Par.cls_int_of_std _ rfl) (Par.cls_dual_of_std _ rfl h.pz_norm)
  refine ⟨⟨H.conj (pz : H.E), map_isIntegral_int (H.conj : H.E →+* H.E) (RingOfIntegers.isIntegral_coe pz)⟩, ?_⟩
  apply RingOfIntegers.ext
  show H.conj (pz : H.E) * (pz : H.E) = ((T : 𝓞 H.E) : H.E)
  rw [mul_comm, h.pz_norm]
  simp

end Formalism.MainNotions.Gaps.LG

end
