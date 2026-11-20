import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFrameCm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexConjLevelVL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RingEquivAdicCompletionMemIntegersIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemIntVIffOfSplitting
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitStabGLIffMemRange
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexCongPre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.LevelIndex

section Group

variable {G G' : Type} [Group G] [Group G']

/- English proof (translation)
Rewrite using `[← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K (le_inf h1 h2) inf_le_left, ← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K' (le_inf h1 h2) inf_le_right, Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, h]`.
-/
theorem relIndex_eq_of_symm {U K K' : Subgroup G} (h : K'.relIndex K = K.relIndex K') (h1 : U ≤ K)
    (h2 : U ≤ K') : U.relIndex K = U.relIndex K' := by
  rw [← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K (le_inf h1 h2) inf_le_left,
    ← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K' (le_inf h1 h2) inf_le_right,
    Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify `hx` using `[mul_assoc]`. Introduce `h`. Conclude with `⟨_, h, by simp [mul_assoc]⟩`.
-/
theorem mem_map_conj {K : Subgroup G} {γ g : G} :
    g ∈ K.map (MulAut.conj γ).toMonoidHom ↔ γ⁻¹ * g * γ ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

def pull (H : Subgroup G) (p : G →* G') (b : G') (X : Subgroup G') : Subgroup G :=
  H ⊓ X.comap ((MulAut.conj b⁻¹).toMonoidHom.comp p)

/- English proof (translation)
Simplify using `[pull]`.
-/
theorem mem_pull {H : Subgroup G} {p : G →* G'} {b : G'} {X : Subgroup G'} {g : G} :
    g ∈ pull H p b X ↔ g ∈ H ∧ b⁻¹ * p g * b ∈ X := by
  simp [pull]

/- English proof (translation)
Introduce `_ hg` and use `mem_pull.2 ⟨(mem_pull.1 hg).1, h (mem_pull.1 hg).2⟩`.
-/
theorem pull_mono (H : Subgroup G) (p : G →* G') (b : G') {X Y : Subgroup G'} (h : X ≤ Y) :
    pull H p b X ≤ pull H p b Y := fun _ hg => mem_pull.2 ⟨(mem_pull.1 hg).1, h (mem_pull.1 hg).2⟩

/- English proof (translation)
Establish `h1 : (pull H p b X).relIndex (pull H p b Y) = (X.comap ((MulAut.conj b⁻¹).toMonoidHom.comp p)).relIndex (pull H p b Y)`. Unfold `Subgroup.relIndex`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_subgroupOf]`.

Conclude with `⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩`. Rewrite using `[h1, Subgroup.relIndex_comap]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `hg.2`. Introduce `hy`. Take `⟨g, hg, e⟩` from `hs (b * y * b⁻¹)`. Use `⟨g, mem_pull.2 ⟨hg, ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify `hy` using `[e, mul_assoc]`. Simplify using `[e, mul_assoc]`.
-/
theorem relIndex_pull {H : Subgroup G} {p : G →* G'} (hs : ∀ y, ∃ g ∈ H, p g = y) (b : G')
    (X Y : Subgroup G') : (pull H p b X).relIndex (pull H p b Y) = X.relIndex Y := by
  have h1 : (pull H p b X).relIndex (pull H p b Y) =
      (X.comap ((MulAut.conj b⁻¹).toMonoidHom.comp p)).relIndex (pull H p b Y) := by
    unfold Subgroup.relIndex
    congr 1
    ext g
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  rw [h1, Subgroup.relIndex_comap]
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.2
  · intro hy
    obtain ⟨g, hg, e⟩ := hs (b * y * b⁻¹)
    refine ⟨g, mem_pull.2 ⟨hg, ?_⟩, ?_⟩
    · simpa [e, mul_assoc] using hy
    · simp [e, mul_assoc]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_map_conj, mem_pull, mem_pull]`. Use `and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ?_` and prove the remaining obligations. Use `mul_mem (mul_mem hγ h) (inv_mem hγ)` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Simplify using `[mul_assoc]`.
-/
theorem map_conj_pull {H : Subgroup G} (p : G →* G') (b : G') (X : Subgroup G') {γ : G} (hγ : γ ∈ H) :
    (pull H p b X).map (MulAut.conj γ).toMonoidHom = pull H p (p γ * b) X := by
  ext g
  rw [mem_map_conj, mem_pull, mem_pull]
  refine and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ?_
  · have := mul_mem (mul_mem hγ h) (inv_mem hγ)
    simpa [mul_assoc] using this
  · simp [mul_assoc]

end Group

section Frames

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `cT τ (b' * b⁻¹).1 * J * (b' * b⁻¹).1 = J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by rw [hb, hb']`.

Use `_ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by`. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem mul_inv_mem_UJ {τ : A →+* A} {J : Matrix n n A} {b b' : GL n A} (hb : cT τ b.1 * J * b.1 = 1)
    (hb' : cT τ b'.1 * J * b'.1 = 1) : b' * b⁻¹ ∈ UJ τ J := by
  change cT τ (b' * b⁻¹).1 * J * (b' * b⁻¹).1 = J
  calc cT τ (b' * b⁻¹).1 * J * (b' * b⁻¹).1
      = cT τ (b⁻¹).1 * (cT τ b'.1 * J * b'.1) * (b⁻¹).1 := by
        rw [Units.val_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by rw [hb, hb']
    _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_map_conj]`. Establish `e : ∀ x, γ.1 *ᵥ ((γ⁻¹ * g * γ).1 *ᵥ x) = g.1 *ᵥ (γ.1 *ᵥ x)` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]`. Use `congr 2`.

Use `group`. Simplify using `only [level, Subgroup.mem_inf]`. Use `and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ⟨fun hg y => ?_, fun hg x => ?_⟩` and prove the remaining obligations. Use `mul_mem (mul_mem hγ h) (inv_mem hγ)` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Establish `e' : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Use `hg ((γ⁻¹).1 *ᵥ y)` as an intermediate fact. Rewrite `this` using `[h, h, e, e']`. Then use the resulting hypothesis. Rewrite using `[h, h, e]`.

Conclude with `hg _`.
-/
theorem map_conj_level {S : Subring A} {τ : A →+* A} {J : Matrix n n A} {Λ Λ' : Submodule S (n → A)}
    {γ : GL n A} (hγ : γ ∈ UJ τ J) (h : ∀ x, x ∈ Λ ↔ γ.1 *ᵥ x ∈ Λ') :
    (level τ J Λ).map (MulAut.conj γ).toMonoidHom = level τ J Λ' := by
  ext g
  rw [mem_map_conj]
  have e : ∀ x, γ.1 *ᵥ ((γ⁻¹ * g * γ).1 *ᵥ x) = g.1 *ᵥ (γ.1 *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  simp only [level, Subgroup.mem_inf]
  refine and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ⟨fun hg y => ?_, fun hg x => ?_⟩
  · have := mul_mem (mul_mem hγ h) (inv_mem hγ)
    simpa [mul_assoc] using this
  · have e' : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have := hg ((γ⁻¹).1 *ᵥ y)
    rwa [h, h, e, e'] at this
  · rw [h, h, e]
    exact hg _

end Frames

section Places

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `(Formalism.UG.P.tjcosets_card_residue v).trans rfl`.
-/
theorem card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) =
      Nat.card (𝓞 F ⧸ v.asIdeal) :=
  (Formalism.UG.P.tjcosets_card_residue v).trans rfl

/- English proof (translation)
Establish `h : Ideal.span {(p : 𝓞 F)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Simplify `Ideal.finite_factors h` using `[Ideal.dvd_span_singleton]`.
-/
theorem finite_over {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  simpa [Ideal.dvd_span_singleton] using Ideal.finite_factors h

/- English proof (translation)
Take `⟨a, b, e⟩ : IsCoprime (p : 𝓞 F) (q : 𝓞 F)` from `Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)`. Conclude with `(Ideal.ne_top_iff_one _).1 v.isPrime.ne_top (e ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2))`.
-/
theorem not_mem_both {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨a, b, e⟩ : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top (e ▸ add_mem (Ideal.mul_mem_left _ _ h1)
    (Ideal.mul_mem_left _ _ h2))

/- English proof (translation)
Rewrite using `[Finset.prod_congr rfl fun v hv => h v (by simpa using hv), Finset.prod_const, ← hf]`. Use `congr 1`. Conclude with `(Nat.card_eq_card_finite_toFinset (finite_over hp)).symm`.
-/
theorem prod_over {p : ℕ} (hp : p.Prime) {f : ℕ}
    (hf : Nat.card {v : HeightOneSpectrum (𝓞 F) // (p : 𝓞 F) ∈ v.asIdeal} = f)
    (a : HeightOneSpectrum (𝓞 F) → ℕ) (c : ℝ) (h : ∀ v, (p : 𝓞 F) ∈ v.asIdeal → (a v : ℝ) = c) :
    ∏ v ∈ (finite_over (F := F) hp).toFinset, (a v : ℝ) = c ^ f := by
  rw [Finset.prod_congr rfl fun v hv => h v (by simpa using hv), Finset.prod_const, ← hf]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset (finite_over hp)).symm

/- English proof (translation)
The claim follows from `Subgroup.map_le_range _ _`.
-/
theorem congPre_le {O K : Type} [CommRing O] [CommRing K] (ι : O →+* K) (I : Ideal O) {n : ℕ}
    (H : Subgroup (GL (Fin n) (O ⧸ I))) : congPre ι I H ≤ (bc (n := Fin n) ι).range :=
  Subgroup.map_le_range _ _

end Places

section Record

open GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E)

def HasFrames (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b : GL (Fin R.k) (E ⊗[F] v.adicCompletion F),
    cT (Formalism.UG.sigR sp.cm.sig (v.adicCompletion F)) b.1 * sp.gram0.map (inclE (F := F) (v.adicCompletion F)) * b.1 = 1 ∧
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v

variable {sp}

/- English proof (translation)
Take `⟨b, hb, hbN⟩` from `hN.2.2 v`. Take `⟨b', hb', hbN'⟩` from `hN'.2.2 v`. Establish `hγ` using `mul_inv_mem_UJ hb hb'`. Establish `e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj (b' * b⁻¹)).toMonoidHom = levelVL sp.cm.sig sp.gram0 v N'` using `map_conj_level hγ fun x => by`. Rewrite using `[hbN, hbN', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]`.

Establish `hu` using `GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1 hN.2.1 v _ hγ`. Rewrite `hu` using `[e]`. Conclude with `relIndex_eq_of_symm hu h h'`.
-/
theorem relIndex_selfDual {N N' : Submodule (𝓞 E) (Fin R.k → E)}
    (hN : HasFrames sp N)
    (hN' : HasFrames sp N')
    (v : HeightOneSpectrum (𝓞 F))
    {U : Subgroup (GL (Fin R.k) (E ⊗[F] v.adicCompletion F))}
    (h : U ≤ levelVL sp.cm.sig sp.gram0 v N) (h' : U ≤ levelVL sp.cm.sig sp.gram0 v N') :
    U.relIndex (levelVL sp.cm.sig sp.gram0 v N) = U.relIndex (levelVL sp.cm.sig sp.gram0 v N') := by
  obtain ⟨b, hb, hbN⟩ := hN.2.2 v
  obtain ⟨b', hb', hbN'⟩ := hN'.2.2 v
  have hγ := mul_inv_mem_UJ hb hb'
  have e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj (b' * b⁻¹)).toMonoidHom =
      levelVL sp.cm.sig sp.gram0 v N' := map_conj_level hγ fun x => by
    rw [hbN, hbN', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
  have hu := GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1
    hN.2.1 v _ hγ
  rw [e] at hu
  exact relIndex_eq_of_symm hu h h'

variable {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)

/- English proof (translation)
Take `⟨b, hb, hbN⟩` from `hN.2.2 v`. Establish `hsw` using `L.splitG_sig i v hv`. Establish `hint` using `GlobalTheory.mem_intV_iff_of_splitting _ _ sp.cm v (GlobalTheory.ringEquiv_adicCompletion_mem_integers_iff _ v) _ hsw`. Establish `hlev` using `GlobalTheory.split_stabGL_iff_mem_range _ _ _ _ _ _ hsw hint _ _ b _ hb hbN`. Establish `hfr` using `L.Uloc_g i v hv`.

Establish `hex` using `GlobalTheory.OverCompare.existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) _ _ hsw`. Generalize the expression as in `bc (n := Fin R.k) ((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom) = p at hlev hfr hex`. Establish `hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y` using `fun y => by`. Take `⟨g, hg, -⟩` from `hex y`. Conclude with `⟨g.1, g.2, hg⟩`.

Establish `hK : levelVL sp.cm.sig sp.gram0 v N = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (p b) (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range`. Use extensionality with `g`. Rewrite using `[mem_pull]`. Conclude with `and_congr_right fun hg => hlev g hg`. Establish `hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (L.frG i v hv) (iwU F R.k v)`.

Use extensionality with `g`. Rewrite using `[mem_pull]`. Conclude with `⟨fun hg => ⟨L.Uloc_le v hg, (hfr g (L.Uloc_le v hg)).1 hg⟩, fun hg => (hfr g hg.1).2 hg.2⟩`. Take `⟨γ, hγ, eγ⟩` from `hsur (L.frG i v hv * (p b)⁻¹)`. Establish `hu` using `GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1 hN.2.1 v _ hγ`.

Establish `e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj γ).toMonoidHom = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (L.frG i v hv) (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range`. Rewrite using `[hK, map_conj_pull _ _ _ hγ, eγ, inv_mul_cancel_right]`. Rewrite `hu` using `[e]`. Rewrite using `[relIndex_eq_of_symm hu h (hU ▸ pull_mono _ _ _ (congPre_le _ _ _)), hU, relIndex_pull hsur, iwU, GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `GlobalTheory.UniIndexPrime.index_upperUni _ _ _ hp ((card_residue v).trans hs)`.
-/
theorem relIndex_at_g {N : Submodule (𝓞 E) (Fin R.k → E)}
    (hN : HasFrames sp N) (i : Fin 2)
    (hp : (gp i).Prime) (v : HeightOneSpectrum (𝓞 F)) (hs : Nat.card (𝓞 F ⧸ v.asIdeal) = gp i)
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    (h : L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) :
    (((L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) : ℕ) : ℝ) =
      idxColLoc (gp i) R.k := by
  obtain ⟨b, hb, hbN⟩ := hN.2.2 v
  have hsw := L.splitG_sig i v hv
  have hint := GlobalTheory.mem_intV_iff_of_splitting _ _ sp.cm v (GlobalTheory.ringEquiv_adicCompletion_mem_integers_iff _ v) _ hsw
  have hlev := GlobalTheory.split_stabGL_iff_mem_range _ _ _ _ _ _ hsw hint _ _ b _ hb hbN
  have hfr := L.Uloc_g i v hv
  have hex := GlobalTheory.OverCompare.existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit sp) _ _ hsw
  generalize bc (n := Fin R.k) ((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom) = p at hlev hfr hex
  have hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y := fun y => by
    obtain ⟨g, hg, -⟩ := hex y
    exact ⟨g.1, g.2, hg⟩
  have hK : levelVL sp.cm.sig sp.gram0 v N =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (p b)
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    ext g
    rw [mem_pull]
    exact and_congr_right fun hg => hlev g hg
  have hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p
      (L.frG i v hv) (iwU F R.k v) := by
    ext g
    rw [mem_pull]
    exact ⟨fun hg => ⟨L.Uloc_le v hg, (hfr g (L.Uloc_le v hg)).1 hg⟩, fun hg => (hfr g hg.1).2 hg.2⟩
  obtain ⟨γ, hγ, eγ⟩ := hsur (L.frG i v hv * (p b)⁻¹)
  have hu := GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1
    hN.2.1 v _ hγ
  have e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj γ).toMonoidHom =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (L.frG i v hv)
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    rw [hK, map_conj_pull _ _ _ hγ, eγ, inv_mul_cancel_right]
  rw [e] at hu
  rw [relIndex_eq_of_symm hu h (hU ▸ pull_mono _ _ _ (congPre_le _ _ _)), hU, relIndex_pull hsur, iwU,
    GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]
  exact GlobalTheory.UniIndexPrime.index_upperUni _ _ _ hp ((card_residue v).trans hs)

/- English proof (translation)
Take `⟨-, -, -, -, -, hex, -, ⟨b, hb, hlev⟩, f, -, -, -, hf, -, -, hUf⟩` from `h`. Establish `hb' : GlobalTheory.OverCompare.IsFrame (partOf (prP φ) (locLat v N)) b` using `hb`. Take `⟨r, hr⟩` from `hb'.exists_row f`. Establish `hst` using `hr.mem_stabFun_iff hb'`. Generalize the expression as in `bc (n := Fin R.k) (prP φ) = p at hlev hst hex hUf`.

Establish `hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y` using `fun y => by`. Take `⟨g, hg, -⟩` from `hex y`. Conclude with `⟨g.1, g.2, hg⟩`. Establish `hK : levelVL sp.cm.sig sp.gram0 v N = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range`. Use extensionality with `g`.

Rewrite using `[mem_pull]`. Conclude with `⟨fun hg => ⟨hg.1, (hlev g hg.1).1 hg⟩, fun hg => (hlev g hg.1).2 hg.2⟩`. Establish `hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (IsLocalRing.maximalIdeal _) (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow r))`. Use extensionality with `g`. Rewrite using `[mem_pull, hUf, hst]`.

Conclude with `⟨fun hg => ⟨hg.1.1, hg.2⟩, fun hg => ⟨(hlev g hg.1).2 (congPre_le _ _ _ hg.2), hg.2⟩⟩`. Rewrite using `[hK, hU, relIndex_pull hsur, GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `GlobalTheory.Proof.StabilizerIndex.index_stabRow _ _ _ A.T_prime ((card_residue v).trans hs) r ((hr.ne_zero_iff hb').1 hf)`.
-/
theorem local_level_relIndex_at_level_prime_selfDual {N : Submodule (𝓞 E) (Fin R.k → E)}
    (v : HeightOneSpectrum (𝓞 F)) (hs : Nat.card (𝓞 F ⧸ v.asIdeal) = A.T)
    (hv : (A.T : 𝓞 F) ∈ v.asIdeal) {φ} (h : LocalAtT L N v hv φ) :
    (((L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) : ℕ) : ℝ) =
      (A.T : ℝ) ^ R.k - 1 := by
  obtain ⟨-, -, -, -, -, hex, -, ⟨b, hb, hlev⟩, f, -, -, -, hf, -, -, hUf⟩ := h
  have hb' : GlobalTheory.OverCompare.IsFrame (partOf (prP φ) (locLat v N)) b := hb
  obtain ⟨r, hr⟩ := hb'.exists_row f
  have hst := hr.mem_stabFun_iff hb'
  generalize bc (n := Fin R.k) (prP φ) = p at hlev hst hex hUf
  have hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y := fun y => by
    obtain ⟨g, hg, -⟩ := hex y
    exact ⟨g.1, g.2, hg⟩
  have hK : levelVL sp.cm.sig sp.gram0 v N =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    ext g
    rw [mem_pull]
    exact ⟨fun hg => ⟨hg.1, (hlev g hg.1).1 hg⟩, fun hg => (hlev g hg.1).2 hg.2⟩
  have hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b
      (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
        (IsLocalRing.maximalIdeal _) (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow r)) := by
    ext g
    rw [mem_pull, hUf, hst]
    exact ⟨fun hg => ⟨hg.1.1, hg.2⟩, fun hg => ⟨(hlev g hg.1).2 (congPre_le _ _ _ hg.2), hg.2⟩⟩
  rw [hK, hU, relIndex_pull hsur, GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]
  exact GlobalTheory.Proof.StabilizerIndex.index_stabRow _ _ _ A.T_prime ((card_residue v).trans hs) r
    ((hr.ne_zero_iff hb').1 hf)

/- English proof (translation)
Use `⟨Formalism.UG.P.afsplitU v x 1, Formalism.UG.P.afsplitU_mem v _ _ _ _ hx (one_mem _), Formalism.UG.P.afsplit_right1 v _ _, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_one (bc (n := Fin R.k) (prV (E := E) w))]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]`.
-/
theorem exists_glue (v : HeightOneSpectrum (𝓞 F))
    (x : GL (Fin R.k) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) :
    ∃ g ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F),
      bc (prV (E := E) v) g = x ∧ ∀ w, w ≠ v → bc (prV (E := E) w) g = 1 := by
  refine ⟨Formalism.UG.P.afsplitU v x 1, Formalism.UG.P.afsplitU_mem v _ _ _ _ hx (one_mem _),
    Formalism.UG.P.afsplit_right1 v _ _, fun w hw => ?_⟩
  rw [← map_one (bc (n := Fin R.k) (prV (E := E) w))]
  apply Units.ext
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
    Formalism.UG.P.afsplitC_prV_ne v w hw]

/- English proof (translation)
Take `⟨hTg, N₀, hN₀, hloc, hle₀, -⟩` from `H`. Establish `hN` using `hfr N hN₁`. Establish `hN₀'` using `hfr N₀ ⟨hN₀.1, hN₀.2.1, hN₀.2.2.1⟩`. Establish `hK` using `GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ sp.cm.sig _ sp.gram0 N hN.1`. Establish `hle : ∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N` using `fun v x hx => by`.

Take `⟨g, hg, e, h1⟩` from `exists_glue v x (L.Uloc_le v hx)`. Establish `hgU : g ∈ L.U` using `(L.U_eq g).2 ⟨hg, fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[e]` and apply the resulting hypothesis.

Rewrite using `[h1 w hw]`. Conclude with `one_mem _⟩`. Conclude with `e ▸ ((hK g).1 (hUK hgU)).2 v`. Establish `hT'` using `A.T_prime`. Establish `hidx` using `GlobalTheory.relIndex_eq_prod_local _ _ _ (fun v => bc (n := Fin R.k) (prV (E := E) v)) _ (levelAfL sp.cm.sig sp.gram0 N) L.U (fun v => levelVL sp.cm.sig sp.gram0 v N) L.Uloc (((finite_over (hp 0)).toFinset ∪ (finite_over (hp 1)).toFinset) ∪ (finite_over hT').toFinset) (fun v x h …`.

Simplify using `only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv`. Establish `e : L.Uloc v = levelVL sp.cm.sig sp.gram0 v N₀`. Rewrite using `[L.Uloc_hyp v hv.1.1 hv.1.2 hv.2]`. Conclude with `congrArg (level _ _) (hN₀.2.2.2.2.2 v hv.2).symm`. Rewrite using `[← Subgroup.relIndex_eq_one, relIndex_selfDual hN hN₀' v (hle v) (hle₀ v), e, Subgroup.relIndex_self])`.

Rewrite using `[hidx, Nat.cast_prod, Finset.prod_union, Finset.prod_union, prod_over (hp 0) (hg 0).1 _ _ fun v hv => relIndex_at_g L hN 0 (hp 0) v ((hg 0).2 v hv) hv (hle v), prod_over (hp 1) (hg 1).1 _ _ fun v hv => relIndex_at_g L hN 1 (hp 1) v ((hg 1).2 v hv) hv (hle v), prod_over hT' hT.1 _ …`. Take `⟨φ, hφ⟩` from `hloc v hv`. Rewrite using `[relIndex_selfDual hN hN₀' v (hle v) (hle₀ v)]`. Conclude with `local_level_relIndex_at_level_prime_selfDual L v (hT.2 v hv) hv hφ]`. Rewrite using `[Finset.disjoint_left]`.

Introduce `v h0 h1`. Conclude with `not_mem_both (hp 0) (hp 1) hne v (by simpa using h0) (by simpa using h1)`. Rewrite using `[Finset.disjoint_left]`. Introduce `v h0 h1`. Break down `Finset.mem_union.1 h0 with h | h` into its components or cases.

Conclude with `not_mem_both hT' (hp 0) (hTg 0) v (by simpa using h1) (by simpa using h)`. Conclude with `not_mem_both hT' (hp 1) (hTg 1) v (by simpa using h1) (by simpa using h)`.
-/
theorem relIndex_level (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) {f : ℕ}
    (hg : ∀ i, Nat.card {v : HeightOneSpectrum (𝓞 F) // (gp i : 𝓞 F) ∈ v.asIdeal} = f ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (gp i : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = gp i)
    (hT : Nat.card {v : HeightOneSpectrum (𝓞 F) // (A.T : 𝓞 F) ∈ v.asIdeal} = f ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = A.T)
    (hfr : ∀ N, IsSelfDualLat (sp.cm.sig : E →+* E) sp.gram0 N → HasFrames sp N)
    (H : HasOverLattice L) {N : Submodule (𝓞 E) (Fin R.k → E)}
    (hN₁ : IsSelfDualLat (sp.cm.sig : E →+* E) sp.gram0 N) (hUK : L.U ≤ levelAfL sp.cm.sig sp.gram0 N) :
    ((L.U.relIndex (levelAfL sp.cm.sig sp.gram0 N) : ℕ) : ℝ) =
      idxColLoc (gp 0) R.k ^ f * idxColLoc (gp 1) R.k ^ f * ((A.T : ℝ) ^ R.k - 1) ^ f := by
  classical
  obtain ⟨hTg, N₀, hN₀, hloc, hle₀, -⟩ := H
  have hN := hfr N hN₁
  have hN₀' := hfr N₀ ⟨hN₀.1, hN₀.2.1, hN₀.2.2.1⟩
  have hK := GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ sp.cm.sig _ sp.gram0 N hN.1
  have hle : ∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N := fun v x hx => by
    obtain ⟨g, hg, e, h1⟩ := exists_glue v x (L.Uloc_le v hx)
    have hgU : g ∈ L.U := (L.U_eq g).2 ⟨hg, fun w => by
      by_cases hw : w = v
      · subst hw; rwa [e]
      · rw [h1 w hw]; exact one_mem _⟩
    exact e ▸ ((hK g).1 (hUK hgU)).2 v
  have hT' := A.T_prime
  have hidx := GlobalTheory.relIndex_eq_prod_local _ _ _ (fun v => bc (n := Fin R.k) (prV (E := E) v)) _
    (levelAfL sp.cm.sig sp.gram0 N) L.U (fun v => levelVL sp.cm.sig sp.gram0 v N) L.Uloc
    (((finite_over (hp 0)).toFinset ∪ (finite_over (hp 1)).toFinset) ∪ (finite_over hT').toFinset)
    (fun v x hx => exists_glue v x hx.1) hK L.U_eq (fun v hv => by
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
      have e : L.Uloc v = levelVL sp.cm.sig sp.gram0 v N₀ := by
        rw [L.Uloc_hyp v hv.1.1 hv.1.2 hv.2]
        exact congrArg (level _ _) (hN₀.2.2.2.2.2 v hv.2).symm
      rw [← Subgroup.relIndex_eq_one, relIndex_selfDual hN hN₀' v (hle v) (hle₀ v), e,
        Subgroup.relIndex_self])
  rw [hidx, Nat.cast_prod, Finset.prod_union, Finset.prod_union,
    prod_over (hp 0) (hg 0).1 _ _ fun v hv => relIndex_at_g L hN 0 (hp 0) v ((hg 0).2 v hv) hv (hle v),
    prod_over (hp 1) (hg 1).1 _ _ fun v hv => relIndex_at_g L hN 1 (hp 1) v ((hg 1).2 v hv) hv (hle v),
    prod_over hT' hT.1 _ ((A.T : ℝ) ^ R.k - 1) fun v hv => by
      obtain ⟨φ, hφ⟩ := hloc v hv
      rw [relIndex_selfDual hN hN₀' v (hle v) (hle₀ v)]
      exact local_level_relIndex_at_level_prime_selfDual L v (hT.2 v hv) hv hφ]
  · rw [Finset.disjoint_left]
    intro v h0 h1
    exact not_mem_both (hp 0) (hp 1) hne v (by simpa using h0) (by simpa using h1)
  · rw [Finset.disjoint_left]
    intro v h0 h1
    rcases Finset.mem_union.1 h0 with h | h
    · exact not_mem_both hT' (hp 0) (hTg 0) v (by simpa using h1) (by simpa using h)
    · exact not_mem_both hT' (hp 1) (hTg 1) v (by simpa using h1) (by simpa using h)

end Record

open GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection in

/- English proof (translation)
Introduce `D Lv u`. Use `letI := D.host.cmStar`. Introduce `hg hT N hN hUK`. Conclude with `relIndex_level (Lv u) D.host.g_prime D.host.g_ne hg hT (fun N hN => ⟨hN.1, hN.2.1, fun v => GlobalTheory.SelfDualFrame.exists_frame D N v hN⟩) (H D Lv u hT) hN hUK`.
-/
theorem indexKU_of_selfDualOverBase (H : SelfDualOverBase) : IndexKU := by
  intro D Lv u
  letI := D.host.cmStar
  intro hg hT N hN hUK
  exact relIndex_level (Lv u) D.host.g_prime D.host.g_ne hg hT
    (fun N hN => ⟨hN.1, hN.2.1, fun v => GlobalTheory.SelfDualFrame.exists_frame D N v hN⟩) (H D Lv u hT) hN hUK

end GlobalTheory.LevelIndex
