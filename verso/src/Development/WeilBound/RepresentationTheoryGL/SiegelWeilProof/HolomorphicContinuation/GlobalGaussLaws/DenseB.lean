import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD

noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]`. Simplify using the standard rewrite rules.
-/
theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

/- English proof (translation)
Establish `h1 : Aᴴ * (A⁻¹)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]`. Establish `h2 : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul _ hA`. Simplify using `only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero]`. Simplify using `[h1, h2]`.
-/
theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

/- English proof (translation)
Simplify using `only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[add_comm]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

/- English proof (translation)
Rewrite using `[hpart, hb, ← two_smul ℂ b, smul_smul]`. Evaluate the numerical expressions.
-/
theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

/- English proof (translation)
Establish `h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ` using `(continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose`. Conclude with `h.const_smul (1 / 2 : ℂ)`.
-/
theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

/- English proof (translation)
Simplify using `[nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`.
-/
theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

/- English proof (translation)
The claim follows from `Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const`.
-/
theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

/- English proof (translation)
Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Use `show Continuous fun A => nU (hpart A)`. Conclude with `continuous_nU.comp continuous_hpart`. Use `show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹`. Establish `e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A)`.

Use function extensionality and compare the values at `A`. Conclude with `Matrix.inv_eq_right_inv (nU_mul_neg _)`. Rewrite using `[e]`. Conclude with `continuous_nU.comp continuous_hpart.neg`.
-/
theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg

open Classical in

def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

/- English proof (translation)
Unfold `mlE`. Conclude with `dif_pos h`.
-/
theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

/- English proof (translation)
Establish `: {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0}` using `Set.ext fun A => isUnit_iff_ne_zero`. Rewrite using `[this]`. Conclude with `isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))`.
-/
theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

/- English proof (translation)
Establish `e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate`. Use function extensionality and compare the values at `A`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[e]`. Establish `h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det}` using `ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn fun A hA => isUnit_iff_ne_zero.1 hA`.

Establish `h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate` using `Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))`. Conclude with `h1.smul h2.continuousOn`.
-/
theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

/- English proof (translation)
Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Establish `h1 : (A⁻¹)ᴴ * Aᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]`.
-/
theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

/- English proof (translation)
Establish `hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ))` using `Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal`. Rewrite using `[hind.continuousOn_iff]`. Establish `hi` using `continuousOn_inv_mat (n := n)`. Establish `hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det}`. Rewrite using `[continuousOn_iff_continuous_restrict]`.

Establish `hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹` using `hi.restrict`. Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Conclude with `Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const hi'.matrix_conjTranspose`. Conclude with `MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const continuous_subtype_val.matrix_conjTranspose)`. Use `ContinuousOn.congr hc fun A hA => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, mlE_of hA]`. Use `show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _`. Rewrite using `[inv_mL hA]`.
-/
theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

/- English proof (translation)
Establish `hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ)` using `DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ`. Establish `h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)`. Rewrite using `[hd.closure_range]`. Conclude with `⟨A, trivial, rfl⟩`. Establish `h2` using `image_closure_subset_closure_image continuous_nuE h1`.

Rewrite `h2` using `[← Set.range_comp]`. Then use the resulting hypothesis.
-/
theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

/- English proof (translation)
Establish `hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ)` using `DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ`. Establish `hc : ContinuousAt (mlE (n` using `n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`. Establish `h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A` using `Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)`.

Take `⟨U, hU, hUo, hAU⟩` from `mem_nhds_iff.1 h1`. Take `⟨e, he⟩` from `hd.exists_mem_open hUo ⟨A, hAU⟩`. Conclude with `⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩`.
-/
theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
