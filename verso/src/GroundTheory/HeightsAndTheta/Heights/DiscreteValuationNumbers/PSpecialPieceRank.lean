import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Reduction

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [coeff_map, coeff_weightedHomogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_residue_weightedHomogeneousComponent (m : K → ℕ) (f : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) (weightedHomogeneousComponent (blockWeight ι) m f) =
      weightedHomogeneousComponent (blockWeight ι) m (MvPolynomial.map (IsLocalRing.residue O) f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_weightedHomogeneousSubmodule]`. Rewrite using `[← weightedHomogeneousComponent_eq_self hf, map_residue_weightedHomogeneousComponent]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.
-/
theorem map_residue_mem_weightedHomogeneousSubmodule {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m) :
    MvPolynomial.map (IsLocalRing.residue O) f ∈
      weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m := by
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← weightedHomogeneousComponent_eq_self hf, map_residue_weightedHomogeneousComponent]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/- English proof (translation)
Take `⟨f, rfl⟩` from `MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g`. Use `⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Rewrite using `[map_residue_weightedHomogeneousComponent]`.

Conclude with `weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)`.
-/
theorem exists_form_map_residue_eq {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
  refine ⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [map_residue_weightedHomogeneousComponent]
    exact weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)

/- English proof (translation)
Establish `hfh` using `(mem_weightedHomogeneousSubmodule _ _ _ _).1 hf`. Take `⟨p, hp, hpf⟩` from `(Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP`. Establish `hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P` using `hP p hp m`. Establish `hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈ RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _)`. Rewrite using `[RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf, weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]`.

Rewrite `hker` using `[MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨g, hg⟩` from `hker`. Use `⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.

Establish `h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g = f - weightedHomogeneousComponent (blockWeight ι) m p`. Rewrite using `[C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh, weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_add_mul_of_map_residue_mem {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by
  have hfh := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hf
  obtain ⟨p, hp, hpf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP
  have hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P := hP p hp m
  have hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈
      RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf,
      weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1
        (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · have h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g =
        f - weightedHomogeneousComponent (blockWeight ι) m p := by
      rw [C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh,
        weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
    rw [h2]
    ring

end Reduction

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m`. Take `⟨hfree, hfin⟩` from `h1 O ϖ hϖ K ι P htor m`. Set `ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O)` to `mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))`. Establish `hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f` using `fun f => rfl`. Establish `hle : P ≤ (specialIdeal P).comap ρ` using `fun x hx => by`.

Rewrite using `[Ideal.mem_comap, hρ]`. Conclude with `Ideal.mem_map_of_mem _ hx`. Set `T` to `Ideal.quotientMapₐ (specialIdeal P) ρ hle`. Establish `hT : ∀ f, T (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f)` using `fun f => rfl`. Establish `hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m`.

Introduce `y hy`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.1 hy`. Conclude with `Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩`. Set `b` to `Module.Free.chooseBasis O (gradedPieceR P m)`. Set `v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m` to `fun i => ⟨T (b i), hTM _ (b i).2⟩`.

Establish `hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i)` using `fun i => rfl`. Establish `hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P), IsLocalRing.residue O c • x = c • x` using `fun c x => by`. Rewrite using `[← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]`. Establish `hli : LinearIndependent (IsLocalRing.ResidueField O) v`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `choose c hc using fun j => IsLocalRing.residue_surjective (g j)`. Set `y : gradedPieceR P m` to `∑ j, c j • b j`. Take `⟨f, hf, hfy⟩` from `Submodule.mem_map.1 y.2`. Establish `hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P)` using `hfy`.

Establish `h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0`. Rewrite using `[← hT, hfy']`. Establish `hg'` using `congrArg Subtype.val hg`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'`. Simplify using `only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]`.

Rewrite using `[← hg']`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hc j, hsmul]`. Take `⟨p, hp, g0, hg0, hfp⟩` from `exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)`. Set `z : gradedPieceR P m` to `⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩`.

Establish `hyz : y = ϖ • z`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hfy', hfp, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul, Submodule.coe_smul]`. Use `show _ = ϖ • Ideal.Quotient.mk P g0`. Rewrite using `[← map_mul, C_mul']`.

Conclude with `map_smul (Ideal.Quotient.mkₐ O P) ϖ g0`. Establish `hbli` using `b.linearIndependent`. Rewrite `hbli` using `[Fintype.linearIndependent_iff]`. Establish `key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0`. Establish `e1 : ∑ j, (c j - ϖ * b.repr z j) • b j = ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j`.

Rewrite using `[Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `(sub_smul (c j) (ϖ * b.repr z j) (b j)).trans (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))`. Rewrite using `[e1, b.sum_repr]`. Conclude with `sub_eq_zero.2 hyz`.

Establish `hi` using `hbli _ key i`. Rewrite using `[← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]`. Establish `hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v)`. Introduce and unpack `⟨x, hx⟩ -`. Take `⟨g, hg, rfl⟩` from `Submodule.mem_map.1 hx`.

Take `⟨f, hf, rfl⟩` from `exists_form_map_residue_eq hg`. Set `y : gradedPieceR P m` to `⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `hy` using `congrArg Subtype.val (b.sum_repr y)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢`. Express the relevant statement in the definitionally equal form `_ = T (y : MRing ι O ⧸ P)`. Rewrite using `[← hy, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hv, hsmul]`. Rewrite using `[Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]`.
-/
theorem SpecialPieceRank.proof (h1 : GradedPieceFree.Statement.{u}) : SpecialPieceRank.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m
  obtain ⟨hfree, hfin⟩ := h1 O ϖ hϖ K ι P htor m
  let ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O) :=
    mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))
  have hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f := fun f => rfl
  have hle : P ≤ (specialIdeal P).comap ρ := fun x hx => by
    rw [Ideal.mem_comap, hρ]
    exact Ideal.mem_map_of_mem _ hx
  let T := Ideal.quotientMapₐ (specialIdeal P) ρ hle
  have hT : ∀ f, T (Ideal.Quotient.mk P f) =
      Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) := fun f => rfl
  have hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩
  let b := Module.Free.chooseBasis O (gradedPieceR P m)
  let v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m :=
    fun i => ⟨T (b i), hTM _ (b i).2⟩
  have hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i) := fun i => rfl
  have hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P),
      IsLocalRing.residue O c • x = c • x := fun c x => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hli : LinearIndependent (IsLocalRing.ResidueField O) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun j => IsLocalRing.residue_surjective (g j)
    let y : gradedPieceR P m := ∑ j, c j • b j
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 y.2
    have hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P) := hfy
    have h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0 := by
      rw [← hT, hfy']
      have hg' := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'
      simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      rw [← hg']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j, hsmul]
    obtain ⟨p, hp, g0, hg0, hfp⟩ :=
      exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let z : gradedPieceR P m := ⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩
    have hyz : y = ϖ • z := by
      apply Subtype.ext
      rw [← hfy', hfp, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul,
        Submodule.coe_smul]
      show _ = ϖ • Ideal.Quotient.mk P g0
      rw [← map_mul, C_mul']
      exact map_smul (Ideal.Quotient.mkₐ O P) ϖ g0
    have hbli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbli
    have key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0 := by
      have e1 : ∑ j, (c j - ϖ * b.repr z j) • b j =
          ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (sub_smul (c j) (ϖ * b.repr z j) (b j)).trans
          (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))
      rw [e1, b.sum_repr]
      exact sub_eq_zero.2 hyz
    have hi := hbli _ key i
    rw [← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := exists_form_map_residue_eq hg
    let y : gradedPieceR P m := ⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢
    change _ = T (y : MRing ι O ⧸ P)
    rw [← hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hv, hsmul]
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
