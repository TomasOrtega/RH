import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.MulVecMemLf

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

/- English proof (translation)
The claim follows from `isCompact_Ohat.image (continuous_const.mul continuous_id)`.
-/
theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

/- English proof (translation)
The claim follows from `ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))`.
-/
theorem ctsA_fst (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.1 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))

/- English proof (translation)
The claim follows from `ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))`.
-/
theorem ctsA_snd (i j : Fin I.n) : CtsA (bs I) (fun p : Co I × Co I => matOf I p.2 i j) :=
  ctsA_emb ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Conclude with `ctsA_sum _ fun l _ => ctsA_mul (hf i l) (hg l j)`.
-/
theorem ctsA_mulE {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => (f p * g p) i j) := by
  simp only [Matrix.mul_apply]
  exact ctsA_sum _ fun l _ => ctsA_mul (hf i l) (hg l j)

/- English proof (translation)
The claim follows from `ctsA_const _`.
-/
theorem ctsA_constE (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (i j : Fin I.n) :
    CtsA (bs I) (fun _ : Co I × Co I => M i j) := ctsA_const _

/- English proof (translation)
Use `show CtsA (bs I) (fun p => Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (f p j i))`. Conclude with `ctsA_map _ (hf j i)`.
-/
theorem ctsA_cTE {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => Formalism.UG.cT (sg I) (f p) i j) := by
  show CtsA (bs I) (fun p => Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (f p j i))
  exact ctsA_map _ (hf j i)

/- English proof (translation)
Establish `: {p | f p = g p} = ⋂ i, ⋂ j, {p | f p i j = g p i j}`. Use extensionality with `p`. Simplify using `[← Matrix.ext_iff]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eqA (bs I) (hf i j) (hg i j)`.
-/
theorem isClosed_matEq {f g : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (hg : ∀ i j, CtsA (bs I) (fun p => g p i j)) :
    IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = ⋂ i, ⋂ j, {p | f p i j = g p i j} := by
    ext p; simp [← Matrix.ext_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eqA (bs I) (hf i j) (hg i j)

/- English proof (translation)
Establish `: {p | ∀ l ∈ I.L, f p *ᵥ inclV (F` using `I.F) l ∈ I.Lf} = ⋂ l ∈ I.L, {p | f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by ext; simp`. Rewrite using `[this]`. Use `isClosed_biInter fun l _ => ?_` and prove the remaining obligations. Establish `hc : Continuous (fun p => fun j => coord (bs I) ((f p *ᵥ inclV (F` using `I.F) l) j)) := by`. Use `continuous_pi fun j => ?_` and prove the remaining obligations.

Establish `: CtsA (bs I) (fun p => (f p *ᵥ inclV (F` using `I.F) l) j) := by`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `ctsA_sum _ fun k _ => ctsA_mul (hf j k) (ctsA_const _)`. Conclude with `this`. Use `(isClosed_LfC I d hd hlow).preimage hc` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `p`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, emb_coord]`.
-/
theorem isClosed_lat (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) :
    IsClosed {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
  have : {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} =
      ⋂ l ∈ I.L, {p | f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
    ext; simp
  rw [this]
  refine isClosed_biInter fun l _ => ?_
  have hc : Continuous (fun p => fun j => coord (bs I) ((f p *ᵥ inclV (F := I.F) l) j)) := by
    refine continuous_pi fun j => ?_
    have : CtsA (bs I) (fun p => (f p *ᵥ inclV (F := I.F) l) j) := by
      simp only [Matrix.mulVec, dotProduct]
      exact ctsA_sum _ fun k _ => ctsA_mul (hf j k) (ctsA_const _)
    exact this
  have := (isClosed_LfC I d hd hlow).preimage hc
  convert this using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, emb_coord]

/- English proof (translation)
Establish `hbox : IsCompact {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N}`. Establish `: {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} = (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) ×ˢ (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N)`. Use extensionality with `p`. Simplify using `only [Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq]`. Conclude with `⟨fun h => ⟨fun i j k => (h i j k).1, fun i j k => (h i j k).2⟩, fun h i j k => ⟨h.1 i j k, h.2 i j k⟩⟩`.

Rewrite using `[this]`. Establish `h3` using `isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : ιb I => isCompact_Bx I N`. Conclude with `h3.prod h3`. Establish `hf` using `ctsA_fst I`. Establish `hs` using `ctsA_snd I`.

Establish `hc1` using `isClosed_matEq I (ctsA_mulE I hf hs) (ctsA_constE I 1)`. Establish `hc2` using `isClosed_matEq I (ctsA_mulE I hs hf) (ctsA_constE I 1)`. Establish `hc3` using `isClosed_matEq I (ctsA_mulE I (ctsA_mulE I (ctsA_cTE I hf) (ctsA_constE I (Jf I))) hf) (ctsA_constE I (Jf I))`. Establish `hc4` using `isClosed_lat I d hd hlow hf`. Establish `hc5` using `isClosed_lat I d hd hlow hs`.

Conclude with `hbox.inter_right (hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5))))`.
-/
theorem isCompact_Cset (N d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsCompact (Cset I N) := by
  have hbox : IsCompact {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} := by
    have : {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} =
        (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) ×ˢ
          (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨fun i j k => (h i j k).1, fun i j k => (h i j k).2⟩,
        fun h i j k => ⟨h.1 i j k, h.2 i j k⟩⟩
    rw [this]
    have h3 := isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n =>
      isCompact_univ_pi fun _ : ιb I => isCompact_Bx I N
    exact h3.prod h3
  have hf := ctsA_fst I
  have hs := ctsA_snd I
  have hc1 := isClosed_matEq I (ctsA_mulE I hf hs) (ctsA_constE I 1)
  have hc2 := isClosed_matEq I (ctsA_mulE I hs hf) (ctsA_constE I 1)
  have hc3 := isClosed_matEq I (ctsA_mulE I (ctsA_mulE I (ctsA_cTE I hf) (ctsA_constE I (Jf I))) hf)
    (ctsA_constE I (Jf I))
  have hc4 := isClosed_lat I d hd hlow hf
  have hc5 := isClosed_lat I d hd hlow hs
  exact hbox.inter_right (hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5))))

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

/- English proof (translation)
Introduce `y`. Establish `h1` using `mulVec_mem_Lf I _ p.2.2.2.2.2.1`. Establish `h2` using `mulVec_mem_Lf I _ p.2.2.2.2.2.2`. Use `show y ∈ I.Lf ↔ matOf I p.1.1 *ᵥ y ∈ I.Lf`. Prove the components needed by the constructor for the conclusion.

Conclude with `h1 y`. Introduce `hy`. Use `h2 _ hy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, p.2.2.2.1, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem psi_mem (N : ℕ) (p : Cset I N) : psi I N p ∈ I.Kset := by
  intro y
  have h1 := mulVec_mem_Lf I _ p.2.2.2.2.2.1
  have h2 := mulVec_mem_Lf I _ p.2.2.2.2.2.2
  show y ∈ I.Lf ↔ matOf I p.1.1 *ᵥ y ∈ I.Lf
  constructor
  · exact h1 y
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, p.2.2.2.1, Matrix.one_mulVec] at this

end Cpt

end PI.WAU
