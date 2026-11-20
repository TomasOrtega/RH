import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (radical)

noncomputable section
namespace GlobalTheory.TypeConstLoc

open GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic ValuativeRel

section Blocks

variable {R : Type} [CommRing R] {a b r : ℕ}

/- English proof (translation)
Rewrite using `[GlobalTheory.RadRev.mem_unipRad_entries]`. Simplify using `only [radical, Set.mem_setOf_eq, ← he]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hne`. Assume the negation of the conclusion as `hc`.

Conclude with `hne (h i j hc)`. Introduce `h i j hc`. Assume the negation of the conclusion as `hne`. Conclude with `hc (h i j hne)`.
-/
theorem mem_unipRad_iff_radical {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] {e : (Σ c, m c) ≃ Fin r}
    (he : ∀ i j : Fin r, blk e i < blk e j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ)) {g : GL (Fin r) R} :
    g ∈ unipRad R e ↔ g ∈ radical R r a := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  simp only [radical, Set.mem_setOf_eq, ← he]
  constructor
  · intro h i j hne
    by_contra hc
    exact hne (h i j hc)
  · intro h i j hc
    by_contra hne
    exact hc (h i j hne)

/- English proof (translation)
Take `⟨⟨c, i'⟩, rfl⟩` from `(stdBlocks ![a, b] h').surjective i`. Rewrite using `[blk_apply]`. Use `stdBlocks_val ![a, b] h' c i'` as an intermediate fact. Use `fin_cases c`. Establish `hi` using `i'.2`.

Simplify using `at this hi ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hi` using `i'.2`. Simplify using `at this hi ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem blk_stdBlocks (h' : ∑ c, ![a, b] c = r) (i : Fin r) :
    blk (stdBlocks ![a, b] h') i = if (i : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![a, b] h').surjective i
  rw [blk_apply]
  have := stdBlocks_val ![a, b] h' c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

/- English proof (translation)
Take `⟨⟨c, i'⟩, rfl⟩` from `(two (stdSum h)).surjective i`. Rewrite using `[blk_apply]`. Consider the cases of `c`. Establish `hi : ((i' : Fin a) : ℕ) < a` using `(i' : Fin a).2`. Rewrite using `[two_false, stdSum_inl]`.

Simplify using `[hi]`. Rewrite using `[two_true, stdSum_inr]`. Simplify using the standard rewrite rules.
-/
theorem blk_two (h : a + b = r) (i : Fin r) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (two (stdSum h)).surjective i
  rw [blk_apply]
  cases c
  · have hi : ((i' : Fin a) : ℕ) < a := (i' : Fin a).2
    rw [two_false, stdSum_inl]
    simp [hi]
  · rw [two_true, stdSum_inr]
    simp

/- English proof (translation)
The claim follows from `mem_unipRad_iff_radical fun i j => by rw [blk_stdBlocks, blk_stdBlocks] by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega`.
-/
theorem mem_unipRad_stdBlocks_iff (h' : ∑ c, ![a, b] c = r) {g : GL (Fin r) R} :
    g ∈ unipRad R (stdBlocks ![a, b] h') ↔ g ∈ radical R r a :=
  mem_unipRad_iff_radical fun i j => by
    rw [blk_stdBlocks, blk_stdBlocks]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega

/- English proof (translation)
The claim follows from `mem_unipRad_iff_radical fun i j => by rw [blk_two, blk_two] by_cases hi : a ≤ (i : ℕ) <;> by_cases hj : a ≤ (j : ℕ) <;> simp [hi, hj] <;> omega`.
-/
theorem mem_stdMaxRad_iff (h : a + b = r) {g : GL (Fin r) R} : g ∈ stdMaxRad R h ↔ g ∈ radical R r a :=
  mem_unipRad_iff_radical fun i j => by
    rw [blk_two, blk_two]
    by_cases hi : a ≤ (i : ℕ) <;> by_cases hj : a ≤ (j : ℕ) <;> simp [hi, hj] <;> omega

/- English proof (translation)
Introduce `g hg` and use `by rw [stdMaxParab, mem_parab_two] intro j i have := mem_parab_iff.1 hg 1 0 j i (by decide) have e1 : stdBlocks ![a, b] h' ⟨1, j⟩ = stdSum h (Sum.inr j) := Fin.ext (((stdBlocks_val ![a, b] h' 1 j).trans (congrArg (· + (j : ℕ)) (Fin.sum_univ_one _))).trans (stdSum_inr h j).symm) h …`.
-/
theorem parab_stdBlocks_le (h : a + b = r) (h' : ∑ c, ![a, b] c = r) :
    parab R (stdBlocks ![a, b] h') ≤ stdMaxParab R h := fun g hg => by
  rw [stdMaxParab, mem_parab_two]
  intro j i
  have := mem_parab_iff.1 hg 1 0 j i (by decide)
  have e1 : stdBlocks ![a, b] h' ⟨1, j⟩ = stdSum h (Sum.inr j) :=
    Fin.ext (((stdBlocks_val ![a, b] h' 1 j).trans (congrArg (· + (j : ℕ)) (Fin.sum_univ_one _))).trans
      (stdSum_inr h j).symm)
  have e2 : stdBlocks ![a, b] h' ⟨0, i⟩ = stdSum h (Sum.inl i) :=
    Fin.ext (((stdBlocks_val ![a, b] h' 0 i).trans (zero_add _)).trans (stdSum_inl h i).symm)
  exact e1 ▸ e2 ▸ this

/- English proof (translation)
Introduce `i j hne`. Use `hx i j fun heq => hne ?_` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.map_apply, heq]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem map_mem_radical {S : Type} [CommRing S] (f : R →+* S) {x : GL (Fin r) R} (hx : x ∈ radical R r a) :
    Matrix.GeneralLinearGroup.map f x ∈ radical S r a := by
  intro i j hne
  refine hx i j fun heq => hne ?_
  rw [Matrix.GeneralLinearGroup.map_apply, heq]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Establish `: radical k r a = ⋂ i : Fin r, ⋂ j : Fin r, {u : GL (Fin r) k | ((i : ℕ) < a ∧ a ≤ (j : ℕ)) ∨ (u : Matrix (Fin r) (Fin r) k) i j = (1 : Matrix (Fin r) (Fin r) k) i j}`. Use extensionality with `u`. Simplify using `only [radical, Set.mem_setOf_eq, Set.mem_iInter]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. The claim follows by propositional logic.

Rewrite using `[this]`. Use `isClosed_iInter fun i => isClosed_iInter fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hc : (i : ℕ) < a ∧ a ≤ (j : ℕ)`. Simplify using `[hc]`. Simplify using `only [hc, false_or]`.

Conclude with `isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const`.
-/
theorem isClosed_radical (k : Type) [Field k] [TopologicalSpace k] [T2Space k] (r a : ℕ) :
    IsClosed (radical k r a) := by
  have : radical k r a = ⋂ i : Fin r, ⋂ j : Fin r, {u : GL (Fin r) k |
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) ∨ (u : Matrix (Fin r) (Fin r) k) i j = (1 : Matrix (Fin r) (Fin r) k) i j} := by
    ext u
    simp only [radical, Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    tauto
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hc : (i : ℕ) < a ∧ a ≤ (j : ℕ)
  · simp [hc]
  · simp only [hc, false_or]
    exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Blocks

/- English proof (translation)
Set `e : Subrepresentation (ρ.comp f : Representation ℂ G W) ≃o Subrepresentation ρ` to `{ toFun := fun S => ⟨S.toSubmodule, fun g v hv => by`. Take `⟨x, rfl⟩` from `hf g`. Conclude with `S.apply_mem_toSubmodule x hv⟩`. Use `invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩`. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Use `haveI : IsSimpleOrder (Subrepresentation ρ) := h`. Conclude with `e.isSimpleOrder`.
-/
theorem isIrreducible_comp {G Q W : Type} [Group G] [Group Q] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ Q W) (f : G →* Q) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G W) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G W) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hme : MeasurableEmbedding (e : G → H)` using `e.toHomeomorph.isClosedEmbedding.measurableEmbedding`. Simplify using `only [conv]`. Rewrite using `[hme.integral_map]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `[map_mul, map_inv]`.
-/
theorem conv_map {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (μ : Measure G)
    (f f' : G → ℂ) :
    conv (μ.map e) (fun y => f (e.symm y)) (fun y => f' (e.symm y)) = fun y => conv μ f f' (e.symm y) := by
  funext y
  have hme : MeasurableEmbedding (e : G → H) := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  simp only [conv]
  rw [hme.integral_map]
  congr 1
  funext x
  simp [map_mul, map_inv]

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField v 𝒪[Fv F v] = (v.adicCompletionIntegers F).toSubring := by letI := GlobalTheory.LocalData.complRel v haveI := GlobalTheory.LocalData.isLocalField v haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Co …`.
-/
theorem integer_eq :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    𝒪[Fv F v] = (v.adicCompletionIntegers F).toSubring := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  ext y
  rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
  exact Iff.rfl

def resEquiv :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    𝓀[Fv F v] ≃+* ResF v :=
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : IsLocalRing (v.adicCompletionIntegers F).toSubring :=
    inferInstanceAs (IsLocalRing (v.adicCompletionIntegers F))
  IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr (integer_eq v))

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField v resEquiv v (IsLocalRing.residue _ ⟨x, hx⟩) = IsLocalRing.residue (v.adicCompletionIntegers F) ⟨x, hx'⟩ := rfl`.
-/
theorem resEquiv_residue (x : Fv F v) (hx) (hx') :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    resEquiv v (IsLocalRing.residue _ ⟨x, hx⟩) = IsLocalRing.residue (v.adicCompletionIntegers F) ⟨x, hx'⟩ :=
  rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} {v} (s : SplitAt σ J L v)

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField v Matrix.GeneralLinearGroup.map (resEquiv v).toRingHom (GlobalTheory.LocGL.redK (Fv F v) (Fin n) ⟨s.equiv x, hK⟩) = s.red ⟨x, hx⟩ := by letI := GlobalTheory.LocalData.complRel v haveI := GlobalTheory.LocalData.isLocalField v ext i j rw [Matrix. …`.
-/
theorem map_redK (x : GLoc σ J v) (hx : x ∈ stabLoc σ J L v) (hK) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    Matrix.GeneralLinearGroup.map (resEquiv v).toRingHom (GlobalTheory.LocGL.redK (Fv F v) (Fin n) ⟨s.equiv x, hK⟩) =
      s.red ⟨x, hx⟩ := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, GlobalTheory.LocGL.redK_apply]
  change resEquiv v _ = ((splitRed s.cm s.herm s.selfDual s.isBasis ⟨x, hx⟩ : GL (Fin n) (ResF v)) :
    Matrix (Fin n) (Fin n) (ResF v)) i j
  have hc := coe_stabLocEquiv s.cm s.herm s.selfDual s.isBasis ⟨x, hx⟩ i j
  have hmem : ((s.equiv x : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) i j ∈
      v.adicCompletionIntegers F := by
    change ((splitEquivIn s.cm s.herm s.emb s.basis x : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) i j ∈ _
    rw [← hc]
    exact ((stabLocEquiv s.cm s.herm s.selfDual s.isBasis ⟨x, hx⟩).1 i j).2
  rw [splitRed_val, Matrix.map_apply, resEquiv_residue _ _ _ hmem]
  congr 1
  exact Subtype.ext hc.symm

/- English proof (translation)
The claim follows from `GlobalTheory.LocalData.isLocalField v letI : MeasurableSpace (GL (Fin n) (Fv F v)) := borel _ idemGL (Fv F v) (μ.map s.equiv) (τ.comp (Matrix.GeneralLinearGroup.map (resEquiv v).toRingHom)) = fun y => s.idem μ τ (s.equiv.symm y) := by letI := GlobalTheory.LocalData.complRel v hav …`.
-/
theorem idemGL_eq {W : Type} [AddCommGroup W] [Module ℂ W] (μ : Measure (GLoc σ J v))
    (τ : Representation ℂ (GL (Fin n) (ResF v)) W) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    letI : MeasurableSpace (GL (Fin n) (Fv F v)) := borel _
    idemGL (Fv F v) (μ.map s.equiv) (τ.comp (Matrix.GeneralLinearGroup.map (resEquiv v).toRingHom)) =
      fun y => s.idem μ τ (s.equiv.symm y) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  letI : MeasurableSpace (GL (Fin n) (Fv F v)) := borel _
  haveI : BorelSpace (GL (Fin n) (Fv F v)) := ⟨rfl⟩
  funext y
  obtain ⟨x, rfl⟩ := s.equiv.surjective y
  simp only [ContinuousMulEquiv.symm_apply_apply]
  by_cases hx : x ∈ stabLoc σ J L v
  · have hK : s.equiv x ∈ KO (Fv F v) (Fin n) := s.mem_stabLoc_iff.1 hx
    have hme : MeasurableEmbedding (s.equiv : GLoc σ J v → GL (Fin n) (Fv F v)) :=
      s.equiv.toHomeomorph.isClosedEmbedding.measurableEmbedding
    have hm : (μ.map s.equiv).real (KO (Fv F v) (Fin n) : Set (GL (Fin n) (Fv F v))) =
        μ.real (stabLoc σ J L v : Set (GLoc σ J v)) := by
      rw [Measure.real, Measure.real, hme.map_apply]
      congr 2
      ext z
      exact s.mem_stabLoc_iff.symm
    have hc := map_redK s x hx hK
    have h1 := typeIdem_coe (μ.map s.equiv) (GlobalTheory.LocGL.redK (Fv F v) (Fin n))
      (τ.comp (Matrix.GeneralLinearGroup.map (resEquiv v).toRingHom)) ⟨s.equiv x, hK⟩
    have h2 := typeIdem_coe μ s.red τ ⟨x, hx⟩
    rw [idemGL, SplitAt.idem]
    refine h1.trans (Eq.trans ?_ h2.symm)
    rw [hm, ← hc]
    rfl
  · rw [idemGL, typeIdem_of_notMem _ _ _ (fun h => hx (s.mem_stabLoc_iff.2 h)), SplitAt.idem,
      typeIdem_of_notMem _ _ _ hx]

end Local

/- English proof (translation)
Introduce `HT D V v s a ha har W _ _ _ τ hτ hNF μ _ φ hφ f hf g`. Use `letI := GlobalTheory.LocalData.complRel v`. Use `haveI := GlobalTheory.LocalData.isLocalField v`. Use `letI : MeasurableSpace (GL (Fin V.rank) (Fv D.host.F v)) := borel _`. Use `haveI : BorelSpace (GL (Fin V.rank) (Fv D.host.F v)) := ⟨rfl⟩`.

Take `⟨b, hb⟩ : ∃ b, a + b = V.rank` from `⟨V.rank - a, by omega⟩`. Establish `hb0 : 0 < b` using `by omega`. Establish `h' : ∑ c, ![a, b] c = V.rank` using `by simpa using hb`. Set `ψ` to `resEquiv v`. Set `τ' : Representation ℂ (GL (Fin V.rank) 𝓀[Fv D.host.F v]) W` to `τ.comp (Matrix.GeneralLinearGroup.map ψ.toRingHom)`.

Establish `hτ' : τ'.IsIrreducible` using `isIrreducible_comp τ _ (fun x => ⟨Matrix.GeneralLinearGroup.map ψ.symm.toRingHom x, by ext; simp⟩) hτ`. Establish `hNF' : NoFixed τ' (stdMaxRad 𝓀[Fv D.host.F v] hb)`. Introduce `w hw`. Use `hNF w fun u hu => ?_` and prove the remaining obligations. Use `hw (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u) ((mem_stdMaxRad_iff hb).2 (map_mem_radical _ hu))` as an intermediate fact.

Establish `e : Matrix.GeneralLinearGroup.map ψ.toRingHom (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u) = u` using `by ext; simp`. Express the relevant statement in the definitionally equal form `τ (Matrix.GeneralLinearGroup.map ψ.toRingHom (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u)) w = w at this`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Set `μ' : Measure (GL (Fin V.rank) (Fv D.host.F v))` to `μ.map s.equiv`. Use `haveI : μ'.IsHaarMeasure := s.equiv.isHaarMeasure_map μ`.

Set `φ'` to `fun y => φ (s.equiv.symm y)`. Establish `hφ' : φ' ∈ SB (GL (Fin V.rank) (Fv D.host.F v))` using `⟨hφ.1.comp_continuous s.equiv.symm.continuous, hφ.2.comp_homeomorph s.equiv.symm.toHomeomorph⟩`. Set `f'` to `fun y => f (s.equiv.symm y)`. Establish `hid` using `idemGL_eq s μ τ`. Establish `hf' : f' = conv μ' (idemGL (Fv D.host.F v) μ' τ') φ' ∨ f' = conv μ' φ' (idemGL (Fv D.host.F v) μ' τ')`.

Rewrite using `[hid]`. Break down `hf with rfl | rfl` into its components or cases. Conclude with `Or.inl (conv_map s.equiv μ _ _).symm`. Conclude with `Or.inr (conv_map s.equiv μ _ _).symm`. Establish `key` using `HT (Fv D.host.F v) V.rank a b hb ha hb0 W τ' hτ' hNF' μ' φ' hφ' f' hf' (conjBy g (parab (Fv D.host.F v) (stdBlocks ![a, b] h'))) (conjBy g (unipRad (Fv D.host.F v) (stdBlocks ![a, b] h'))) ⟨2, ![a, b], h', g, rfl, rfl⟩ ⟨g, Subgroup.map_mono (parab_stdBlocks_le hb h')⟩`.

Use `set N := conjBy g (unipRad (Fv D.host.F v) (stdBlocks ![a, b] h')) with hN`. Set `H : Subgroup (GLoc D.sp.cm.sig V.gram v)` to `N.comap (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))`. Establish `hmem : ∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a` using `fun x => by`. Express the relevant statement in the definitionally equal form `s.equiv x ∈ N ↔ _`. Rewrite using `[hN, mem_conjBy, mem_unipRad_stdBlocks_iff]`.

Establish `hHc : IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v))`. Establish `: (H : Set (GLoc D.sp.cm.sig V.gram v)) = (fun x => g⁻¹ * s.equiv x * g) ⁻¹' radical _ V.rank a` using `Set.ext hmem`. Rewrite using `[this]`. Conclude with `(isClosed_radical _ _ _).preimage ((continuous_const.mul s.equiv.continuous).mul continuous_const)`. Use `⟨H, hHc, hmem, ?_⟩` and prove the remaining obligations.

Use `haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `⟨Measure.haar, inferInstance, fun x y => ?_⟩` and prove the remaining obligations. Set `Φ : H ≃ₜ* N` to `{ toFun := fun u => ⟨s.equiv (u : GLoc D.sp.cm.sig V.gram v), u.2⟩ invFun := fun n => ⟨s.equiv.symm n, show s.equiv (s.equiv.symm n) ∈ N by simpa using n.2⟩ left_inv := fun u => Subtype.ext (s.equiv.symm_apply_apply (u : GLoc D.sp.cm.sig V.gram v)) right_inv := fun n => Subtype.e …`. Use `haveI : ((Measure.haar : Measure H).map Φ).IsHaarMeasure := Φ.isHaarMeasure_map _`. Establish `h0` using `(key ((Measure.haar : Measure H).map Φ) (s.equiv x) (s.equiv y)).2`.

Establish `hme : MeasurableEmbedding (Φ : H → N)` using `Φ.toHomeomorph.isClosedEmbedding.measurableEmbedding`. Rewrite `h0` using `[hme.integral_map]`. Use `Eq.trans ?_ h0` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `u`.

Simplify using `[f', Φ, map_mul]`.
-/
theorem unipIntegral_vanish_splitAt : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (a : ℕ), 0 < a → a < V.rank → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin V.rank) (ResF v)) W), τ.IsIrreducible → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (radical (ResF v) V.rank a) → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) [μ.IsHaarMeasure], ∀ φ ∈ CcLoc D.sp.cm.sig V.gram v, ∀ f : GLoc D.sp.cm.sig V.gram v → ℂ, (f = conv μ (s.idem μ τ) φ ∨ f = conv μ φ (s.idem μ τ)) → ∀ g : GL (Fin V.rank) (Fv D.host.F v), ∃ H : Subgroup (GLoc D.sp.cm.sig V.gram v), IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) ∧ (∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a) ∧ ∃ ν : Measure H, ν.IsHaarMeasure ∧ ∀ x y, ∫ u : H, f (x * u * y) ∂ν = 0 := by
  intro HT D V v s a ha har W _ _ _ τ hτ hNF μ _ φ hφ f hf g
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  letI : MeasurableSpace (GL (Fin V.rank) (Fv D.host.F v)) := borel _
  haveI : BorelSpace (GL (Fin V.rank) (Fv D.host.F v)) := ⟨rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, a + b = V.rank := ⟨V.rank - a, by omega⟩
  have hb0 : 0 < b := by omega
  have h' : ∑ c, ![a, b] c = V.rank := by simpa using hb
  let ψ := resEquiv v
  let τ' : Representation ℂ (GL (Fin V.rank) 𝓀[Fv D.host.F v]) W :=
    τ.comp (Matrix.GeneralLinearGroup.map ψ.toRingHom)
  have hτ' : τ'.IsIrreducible := isIrreducible_comp τ _ (fun x =>
    ⟨Matrix.GeneralLinearGroup.map ψ.symm.toRingHom x, by ext; simp⟩) hτ
  have hNF' : NoFixed τ' (stdMaxRad 𝓀[Fv D.host.F v] hb) := by
    intro w hw
    refine hNF w fun u hu => ?_
    have := hw (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u)
      ((mem_stdMaxRad_iff hb).2 (map_mem_radical _ hu))
    have e : Matrix.GeneralLinearGroup.map ψ.toRingHom (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u) = u := by
      ext; simp
    change τ (Matrix.GeneralLinearGroup.map ψ.toRingHom (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom u)) w = w
      at this
    rwa [e] at this
  let μ' : Measure (GL (Fin V.rank) (Fv D.host.F v)) := μ.map s.equiv
  haveI : μ'.IsHaarMeasure := s.equiv.isHaarMeasure_map μ
  let φ' := fun y => φ (s.equiv.symm y)
  have hφ' : φ' ∈ SB (GL (Fin V.rank) (Fv D.host.F v)) :=
    ⟨hφ.1.comp_continuous s.equiv.symm.continuous, hφ.2.comp_homeomorph s.equiv.symm.toHomeomorph⟩
  let f' := fun y => f (s.equiv.symm y)
  have hid := idemGL_eq s μ τ
  have hf' : f' = conv μ' (idemGL (Fv D.host.F v) μ' τ') φ' ∨ f' = conv μ' φ' (idemGL (Fv D.host.F v) μ' τ') := by
    rw [hid]
    rcases hf with rfl | rfl
    · exact Or.inl (conv_map s.equiv μ _ _).symm
    · exact Or.inr (conv_map s.equiv μ _ _).symm
  have key := HT (Fv D.host.F v) V.rank a b hb ha hb0 W τ' hτ' hNF' μ' φ' hφ' f' hf'
    (conjBy g (parab (Fv D.host.F v) (stdBlocks ![a, b] h')))
    (conjBy g (unipRad (Fv D.host.F v) (stdBlocks ![a, b] h'))) ⟨2, ![a, b], h', g, rfl, rfl⟩
    ⟨g, Subgroup.map_mono (parab_stdBlocks_le hb h')⟩
  set N := conjBy g (unipRad (Fv D.host.F v) (stdBlocks ![a, b] h')) with hN
  let H : Subgroup (GLoc D.sp.cm.sig V.gram v) :=
    N.comap (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))
  have hmem : ∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a := fun x => by
    change s.equiv x ∈ N ↔ _
    rw [hN, mem_conjBy, mem_unipRad_stdBlocks_iff]
  have hHc : IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) := by
    have : (H : Set (GLoc D.sp.cm.sig V.gram v)) = (fun x => g⁻¹ * s.equiv x * g) ⁻¹' radical _ V.rank a :=
      Set.ext hmem
    rw [this]
    exact (isClosed_radical _ _ _).preimage ((continuous_const.mul s.equiv.continuous).mul continuous_const)
  refine ⟨H, hHc, hmem, ?_⟩
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine ⟨Measure.haar, inferInstance, fun x y => ?_⟩
  let Φ : H ≃ₜ* N :=
    { toFun := fun u => ⟨s.equiv (u : GLoc D.sp.cm.sig V.gram v), u.2⟩
      invFun := fun n => ⟨s.equiv.symm n, show s.equiv (s.equiv.symm n) ∈ N by simpa using n.2⟩
      left_inv := fun u => Subtype.ext (s.equiv.symm_apply_apply (u : GLoc D.sp.cm.sig V.gram v))
      right_inv := fun n => Subtype.ext (s.equiv.apply_symm_apply n)
      map_mul' := fun u u' => Subtype.ext (by simp)
      continuous_toFun := (s.equiv.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (s.equiv.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  haveI : ((Measure.haar : Measure H).map Φ).IsHaarMeasure := Φ.isHaarMeasure_map _
  have h0 := (key ((Measure.haar : Measure H).map Φ) (s.equiv x) (s.equiv y)).2
  have hme : MeasurableEmbedding (Φ : H → N) := Φ.toHomeomorph.isClosedEmbedding.measurableEmbedding
  rw [hme.integral_map] at h0
  refine Eq.trans ?_ h0
  congr 1
  funext u
  simp [f', Φ, map_mul]

end GlobalTheory.TypeConstLoc
