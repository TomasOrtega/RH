import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.EmEqInr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
section Gen
variable {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Semiring R]
end Gen
def emEq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Fin L.n ⊕ Unit ≃ Fin d.n :=
  Equiv.ofBijective (Sum.elim L.em fun _ => L.i₀) ⟨by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (L.inj h)
    · exact absurd h ((L.rng (L.em a)).2 ⟨a, rfl⟩)
    · exact absurd h.symm ((L.rng (L.em b)).2 ⟨b, rfl⟩)
    · rfl, fun i => by
    by_cases h : i = L.i₀
    · exact ⟨Sum.inr (), h.symm⟩
    · obtain ⟨a, ha⟩ := (L.rng i).1 h
      exact ⟨Sum.inl a, ha⟩⟩
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emEq_inl_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (a : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L (Sum.inl a) = L.em a := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emEq_inr_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Unit) : _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L (Sum.inr u) = L.i₀ := rfl
/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) N]`. Establish `hne : ∀ a, L.em a ≠ L.i₀` using `fun a => (L.rng (L.em a)).2 ⟨a, rfl⟩`. Establish `: N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) = Matrix.fromBlocks N' 0 0 1`. Use extensionality with `(a | a) (b | b)`. Rewrite using `[Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, Matrix.fromBlocks_apply₁₁, ← h1, Matrix.submatrix_apply]`.

Rewrite using `[Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₁₂, (h0 (L.em a)).2, Matrix.one_apply_ne (hne a), Matrix.zero_apply]`. Rewrite using `[Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₁, (h0 (L.em b)).1, Matrix.one_apply_ne (hne b).symm, Matrix.zero_apply]`. Rewrite using `[Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₂, (h0 L.i₀).1, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`.
-/
theorem det_emb_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (N' : Matrix (Fin L.n) (Fin L.n) (AE F E))
    (h0 : ∀ k, N L.i₀ k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) L.i₀ k ∧
      N k L.i₀ = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) k L.i₀)
    (h1 : N.submatrix L.em L.em = N') : N.det = N'.det := by
  rw [← Matrix.det_submatrix_equiv_self (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) N]
  have hne : ∀ a, L.em a ≠ L.i₀ := fun a => (L.rng (L.em a)).2 ⟨a, rfl⟩
  have : N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_k L) = Matrix.fromBlocks N' 0 0 1 := by
    ext (a | a) (b | b)
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, Matrix.fromBlocks_apply₁₁, ← h1, Matrix.submatrix_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₁₂, (h0 (L.em a)).2,
        Matrix.one_apply_ne (hne a), Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₁, (h0 (L.em b)).1,
        Matrix.one_apply_ne (hne b).symm, Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Avac.emEq_inr_k, Matrix.fromBlocks_apply₂₂, (h0 L.i₀).1, Matrix.one_apply_eq,
        Matrix.one_apply_eq]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
/- English proof (translation)
The claim follows from `Sum.map_injective.2 ⟨L.inj, L.inj⟩`.
-/
theorem emm_inj_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Function.Injective (Sum.map L.em L.em) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
/- English proof (translation)
Introduce and unpack `(c | c)`. Simplify using `only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq, reduceCtorEq, or_false]`. Rewrite using `[show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨Sum.inl a, rfl⟩`. Introduce and unpack `⟨(a | a), h⟩`. Conclude with `⟨a, Sum.inl_injective h⟩`. Simplify using `at h`. Simplify using `only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq, reduceCtorEq, false_or]`.

Rewrite using `[show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨Sum.inr a, rfl⟩`. Introduce and unpack `⟨(a | a), h⟩`.

Simplify using `at h`. Conclude with `⟨a, Sum.inr_injective h⟩`.
-/
theorem emm_rng_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : ∀ c, c ∉ I0 L.i₀ ↔ c ∈ Set.range (Sum.map L.em L.em) := by
  rintro (c | c)
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq, reduceCtorEq, or_false]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · exact ⟨a, Sum.inl_injective h⟩
      · simp at h
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq, reduceCtorEq, false_or]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · simp at h
      · exact ⟨a, Sum.inr_injective h⟩
/- English proof (translation)
Introduce `u hu v` and use `L.j_out g u hu v`.
-/
theorem idI_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : L.sd.G) : IdI (I0 L.i₀) (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v
/- English proof (translation)
Establish `hL` using `(L.ok.stdK k).1 hk`. Use `(d.ok.stdK (L.j k)).2 ⟨fun w => ?_, fun k'' hk'' i j => ?_⟩` and prove the remaining obligations. Establish `hI` using `(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k).map (piInf (d.B.emb w))`. Use `(hI.mul hI.ct).eq_one (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L) ?_` and prove the remaining obligations. Rewrite using `[hI.sub_mul _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L), ← Matrix.conjTranspose_submatrix, Matrix.submatrix_map, L.j_in]`.

Conclude with `hL.1 w`. Choose the witnesses or unpack the hypotheses as in `⟨k₀, hk₀, rfl⟩ : ∃ k₀ ∈ ({k, k⁻¹} : Set L.sd.G), k'' = L.j k₀ := by`. Break down `hk'' with rfl | rfl` into its components or cases. Conclude with `⟨k, Or.inl rfl, rfl⟩`. Conclude with `⟨k⁻¹, Or.inr rfl, (map_inv L.j k).symm⟩`.

Distinguish the cases in `hi : i ∈ I0 L.i₀`. Rewrite using `[(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ i hi j).1]`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j`. Distinguish the cases in `hj : j ∈ I0 L.i₀`. Rewrite using `[(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ j hj i).2]`.

Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j`. Take `⟨a, rfl⟩` from `(_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L i).1 hi`. Take `⟨b, rfl⟩` from `(_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L j).1 hj`. Establish `e` using `congrFun (congrFun (L.j_in k₀) a) b`. Rewrite `e` using `[Matrix.submatrix_apply]`.

Rewrite using `[e]`. Conclude with `hL.2 k₀ hk₀ a b`.
-/
theorem j_K_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {k : L.sd.G} (hk : k ∈ L.sd.K) : L.j k ∈ d.K := by
  have hL := (L.ok.stdK k).1 hk
  refine (d.ok.stdK (L.j k)).2 ⟨fun w => ?_, fun k'' hk'' i j => ?_⟩
  · have hI := (_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k).map (piInf (d.B.emb w))
    refine (hI.mul hI.ct).eq_one (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L) ?_
    rw [hI.sub_mul _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L), ← Matrix.conjTranspose_submatrix, Matrix.submatrix_map, L.j_in]
    exact hL.1 w
  · obtain ⟨k₀, hk₀, rfl⟩ : ∃ k₀ ∈ ({k, k⁻¹} : Set L.sd.G), k'' = L.j k₀ := by
      rcases hk'' with rfl | rfl
      · exact ⟨k, Or.inl rfl, rfl⟩
      · exact ⟨k⁻¹, Or.inr rfl, (map_inv L.j k).symm⟩
    by_cases hi : i ∈ I0 L.i₀
    · rw [(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ i hi j).1]; exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
    by_cases hj : j ∈ I0 L.i₀
    · rw [(_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L k₀ j hj i).2]; exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
    obtain ⟨a, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L i).1 hi
    obtain ⟨b, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L j).1 hj
    have e := congrFun (congrFun (L.j_in k₀) a) b
    rw [Matrix.submatrix_apply] at e
    rw [e]
    exact hL.2 k₀ hk₀ a b
/- English proof (translation)
Take `⟨p', t', hp', k', hk', rfl⟩` from `L.ok.hgt.iwa h`. Establish `h21L` using `_root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero L.sd p' t' hp'`. Take `⟨t₂, hp₂, hdet₂⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k L.sd p' h21L`. Establish `hI` using `_root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L p'`. Establish `h21 : (inFrame d.b (L.j p')).toBlocks₂₁ = 0`.

Use extensionality with `a b`. Simplify using `only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]`. Distinguish the cases in `ha : Sum.inr a ∈ I0 L.i₀`. Rewrite using `[(hI _ ha _).1]`. Simplify using the standard rewrite rules.

Distinguish the cases in `hb : Sum.inl b ∈ I0 L.i₀`. Rewrite using `[(hI _ hb _).2]`. Simplify using the standard rewrite rules. Take `⟨a', ha'⟩` from `(_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 ha`. Take `⟨b', hb'⟩` from `(_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 hb`.

Break down `a' with a' | a'` into its components or cases. Simplify using `at ha'`. Break down `b' with b' | b'` into its components or cases. Establish `e` using `congrFun (congrFun (L.j_in p') (Sum.inr a')) (Sum.inl b')`. Simplify using `only [Matrix.submatrix_apply] at e`.

Rewrite using `[← ha', ← hb', e]`. Use `congrFun (congrFun h21L a') b'` as an intermediate fact. Simplify `this` using `[Matrix.toBlocks₂₁]`. Simplify using `at hb'`. Take `⟨t₁, hp₁, hdet₁⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (L.j p') h21`.

Establish `hdet : Matrix.GeneralLinearGroup.det t₁ = Matrix.GeneralLinearGroup.det t₂`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hdet₁, hdet₂]`. Use `_root_.PositivityTheory.SiegelWeilFormula.Avac.det_emb_k L _ _ (fun k => ⟨?_, ?_⟩) ?_` and prove the remaining obligations. Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply]`.

Rewrite using `[(hI _ (Or.inl rfl) _).1]`. Simplify using `[Matrix.one_apply]`. Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply]`. Rewrite using `[(hI _ (Or.inl rfl) _).2]`. Simplify using `[Matrix.one_apply]`.

Use extensionality with `a b`. Establish `e` using `congrFun (congrFun (L.j_in p') (Sum.inl a)) (Sum.inl b)`. Simplify `e` using `[Matrix.toBlocks₁₁]`. Rewrite using `[map_mul, d.ok.hgt.val _ _ hp₁ _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.j_K_k L hk'), L.ok.hgt.val _ _ hp₂ _ hk', hdet]`.
-/
theorem a_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (h : L.sd.G) : d.a (L.j h) = L.a h := by
  obtain ⟨p', t', hp', k', hk', rfl⟩ := L.ok.hgt.iwa h
  have h21L := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero L.sd p' t' hp'
  obtain ⟨t₂, hp₂, hdet₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k L.sd p' h21L
  have hI := _root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L p'
  have h21 : (inFrame d.b (L.j p')).toBlocks₂₁ = 0 := by
    ext a b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
    by_cases ha : Sum.inr a ∈ I0 L.i₀
    · rw [(hI _ ha _).1]; simp
    by_cases hb : Sum.inl b ∈ I0 L.i₀
    · rw [(hI _ hb _).2]; simp
    obtain ⟨a', ha'⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 ha
    obtain ⟨b', hb'⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L _).1 hb
    rcases a' with a' | a'
    · simp at ha'
    rcases b' with b' | b'
    · have e := congrFun (congrFun (L.j_in p') (Sum.inr a')) (Sum.inl b')
      simp only [Matrix.submatrix_apply] at e
      rw [← ha', ← hb', e]
      have := congrFun (congrFun h21L a') b'
      simpa [Matrix.toBlocks₂₁] using this
    · simp at hb'
  obtain ⟨t₁, hp₁, hdet₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (L.j p') h21
  have hdet : Matrix.GeneralLinearGroup.det t₁ = Matrix.GeneralLinearGroup.det t₂ := by
    refine Units.ext ?_
    rw [hdet₁, hdet₂]
    refine _root_.PositivityTheory.SiegelWeilFormula.Avac.det_emb_k L _ _ (fun k => ⟨?_, ?_⟩) ?_
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).1]; simp [Matrix.one_apply]
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).2]; simp [Matrix.one_apply]
    · ext a b
      have e := congrFun (congrFun (L.j_in p') (Sum.inl a)) (Sum.inl b)
      simpa [Matrix.toBlocks₁₁] using e
  rw [map_mul, d.ok.hgt.val _ _ hp₁ _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.j_K_k L hk'), L.ok.hgt.val _ _ hp₂ _ hk', hdet]
/- English proof (translation)
Take `⟨t, hp, hdet⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d q (isQ_21 hq)`. Establish `e : Matrix.GeneralLinearGroup.det t = lam` using `Units.ext (by rw [hdet, det_row (isQ_11 hq).1, (isQ_11 hq).2])`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d hp, e, _root_.PositivityTheory.SiegelWeilFormula.Avac.a_j_k L h]`.
-/
theorem q_ht'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (h : L.sd.G) :
    d.a (q * L.j h) = (absE F E lam : ℝ) * L.a h := by
  obtain ⟨t, hp, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d q (isQ_21 hq)
  have e : Matrix.GeneralLinearGroup.det t = lam :=
    Units.ext (by rw [hdet, det_row (isQ_11 hq).1, (isQ_11 hq).2])
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d hp, e, _root_.PositivityTheory.SiegelWeilFormula.Avac.a_j_k L h]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
