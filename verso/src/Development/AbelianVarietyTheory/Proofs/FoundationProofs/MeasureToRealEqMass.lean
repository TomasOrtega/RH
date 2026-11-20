import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Lev MeasureTheory NumberField Matrix
open Formalism.UG (bc inclE stabAt IsTotDef Jpq)
open Formalism.L2.DIV (UA UQ UR Cl Gam)
open scoped TensorProduct

namespace GlobalTheory.Mass.Levels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hJ : (Jpq p q)ᴴ = Jpq p q` using `by simp [Jpq, Matrix.fromBlocks_conjTranspose]`. Establish `hJJ : Jpq p q * Jpq p q = 1` using `by simp [Jpq, Matrix.fromBlocks_multiply]`. Establish `hH : Gᴴ = G`. Rewrite using `[← hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `h1 : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul _ hG.isUnit`.

Establish `h2 : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hG.isUnit`. Establish `hH' : G⁻¹ᴴ = G⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hH]`. Take `⟨N, rfl⟩ : ∃ N, g = 1 + N` from `⟨g - 1, by abel⟩`. Establish `hN : N * G⁻¹ + G⁻¹ * Nᴴ + G⁻¹ * (Nᴴ * (G * (N * G⁻¹))) = 0`. Establish `e : G * N + Nᴴ * G + Nᴴ * (G * N) = 0`.

Rewrite `hg` using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one]`. Establish `: (1 + Nᴴ) * G * (1 + N) = G + (G * N + Nᴴ * G + Nᴴ * (G * N))` using `by noncomm_ring`. Rewrite `hg` using `[this]`. Conclude with `add_eq_left.1 hg`. Establish `e'` using `congrArg (fun X => G⁻¹ * X * G⁻¹) e`.

Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, h2, Matrix.mul_one] at e'`. Rewrite `e'` using `[← Matrix.mul_assoc G⁻¹ G, h1, Matrix.one_mul]`. Then use the resulting hypothesis. Set `b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `1 + A * (N * G⁻¹) * (Aᴴ * Jpq p q)`. Establish `hb : bᴴ * Jpq p q * b = Jpq p q`. Establish `e : bᴴ * Jpq p q * b = Jpq p q + Jpq p q * A * (N * G⁻¹ + G⁻¹ * Nᴴ + G⁻¹ * (Nᴴ * ((Aᴴ * Jpq p q * A) * (N * G⁻¹)))) * (Aᴴ * Jpq p q)`.

Simplify using `only [b, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hJ, hH', Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hA, hN, Matrix.mul_zero, Matrix.zero_mul, add_zero]`. Establish `hu : IsUnit b`. Use `(Matrix.isUnit_iff_isUnit_det b).2 (Matrix.isUnit_det_of_left_inverse (B := Jpq p q * (bᴴ * Jpq p q)) ?_)` and prove the remaining obligations.

Rewrite using `[Matrix.mul_assoc, hb, hJJ]`. Use `⟨(⟨hu.unit, hb⟩ : Formalism.UG.Upq p q), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `b * A = _`. Simplify using `only [b, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[Matrix.mul_assoc _ _ A, hA, Matrix.mul_assoc A, Matrix.mul_assoc N, h1, Matrix.mul_one]`.
-/
theorem exists_upq_extends {p q n : ℕ} (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G g : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ * Jpq p q * A = G) (hG : G.det ≠ 0) (hg : gᴴ * G * g = G) :
    ∃ b : UpqT p q, UpqT.mat b * A = A * g := by
  have hJ : (Jpq p q)ᴴ = Jpq p q := by simp [Jpq, Matrix.fromBlocks_conjTranspose]
  have hJJ : Jpq p q * Jpq p q = 1 := by simp [Jpq, Matrix.fromBlocks_multiply]
  have hH : Gᴴ = G := by
    rw [← hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hG.isUnit
  have h2 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG.isUnit
  have hH' : G⁻¹ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  obtain ⟨N, rfl⟩ : ∃ N, g = 1 + N := ⟨g - 1, by abel⟩
  have hN : N * G⁻¹ + G⁻¹ * Nᴴ + G⁻¹ * (Nᴴ * (G * (N * G⁻¹))) = 0 := by
    have e : G * N + Nᴴ * G + Nᴴ * (G * N) = 0 := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at hg
      have : (1 + Nᴴ) * G * (1 + N) = G + (G * N + Nᴴ * G + Nᴴ * (G * N)) := by noncomm_ring
      rw [this] at hg
      exact add_eq_left.1 hg
    have e' := congrArg (fun X => G⁻¹ * X * G⁻¹) e
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, h2,
      Matrix.mul_one] at e'
    rwa [← Matrix.mul_assoc G⁻¹ G, h1, Matrix.one_mul] at e'
  let b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := 1 + A * (N * G⁻¹) * (Aᴴ * Jpq p q)
  have hb : bᴴ * Jpq p q * b = Jpq p q := by
    have e : bᴴ * Jpq p q * b = Jpq p q + Jpq p q * A *
        (N * G⁻¹ + G⁻¹ * Nᴴ + G⁻¹ * (Nᴴ * ((Aᴴ * Jpq p q * A) * (N * G⁻¹)))) * (Aᴴ * Jpq p q) := by
      simp only [b, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hJ, hH',
        Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e, hA, hN, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hu : IsUnit b := by
    refine (Matrix.isUnit_iff_isUnit_det b).2 (Matrix.isUnit_det_of_left_inverse
      (B := Jpq p q * (bᴴ * Jpq p q)) ?_)
    rw [Matrix.mul_assoc, hb, hJJ]
  refine ⟨(⟨hu.unit, hb⟩ : Formalism.UG.Upq p q), ?_⟩
  change b * A = _
  simp only [b, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc _ _ A, hA, Matrix.mul_assoc A, Matrix.mul_assoc N, h1, Matrix.mul_one]

/- English proof (translation)
Use `haveI := h (DoubleCoset.mk Γ L g)`. Use `haveI : Nonempty (stabAt Γ L (DoubleCoset.mk Γ L g).out) := ⟨⟨1, one_mem_stabAt _ _ _⟩⟩`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[← stabOrder_mk, ← DoubleCoset.out_eq' _ _ (DoubleCoset.mk _ _ g), stabOrder_mk]`. Conclude with `Nat.card_pos.ne'`.
-/
theorem finite_stabAt_of_out {G : Type} [Group G] {Γ L : Subgroup G}
    (h : ∀ c : Formalism.UG.ClassSet Γ L, Finite (stabAt Γ L c.out)) (g : G) : Finite (stabAt Γ L g) := by
  haveI := h (DoubleCoset.mk Γ L g)
  haveI : Nonempty (stabAt Γ L (DoubleCoset.mk Γ L g).out) := ⟨⟨1, one_mem_stabAt _ _ _⟩⟩
  refine Nat.finite_of_card_ne_zero ?_
  rw [← stabOrder_mk, ← DoubleCoset.out_eq' _ _ (DoubleCoset.mk _ _ g), stabOrder_mk]
  exact Nat.card_pos.ne'

variable {D : D7}

def toLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) :
    Subgroup (HA (Af D.host.F) D.sp.cm.sig V.gram) :=
  (K.subgroupOf (UA D.sp.cm V.gram)).comap
    (swapPts (Af D.host.F) D.sp.cm.sig V.gram : HA (Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram)

variable (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D)))

/- English proof (translation)
The claim follows from `unitaryMass_comap_swapPts _ _ _`.
-/
theorem mass_eq_fin : unitaryMass D.sp.cm.sig V.gram (toLev V K) =
    classMass (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) :=
  unitaryMass_comap_swapPts _ _ _

/- English proof (translation)
Use extensionality with `g`. Express the relevant statement in the definitionally equal form `((swapPts (Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D)) ∈ K ↔ finE V g ∈ K`. Rewrite using `[coe_swapPts, hπ g]`. Both sides reduce to the same expression.
-/
theorem comap_toLev {π : GA D V →* HA (Af D.host.F) D.sp.cm.sig V.gram} (hπ : IsFinProj D.sp.cm.sig V.gram π) :
    (toLev V K).comap π = K.comap (finE V) := by
  ext g
  change ((swapPts (Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D)) ∈ K ↔
    finE V g ∈ K
  rw [coe_swapPts, hπ g]
  rfl

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Rewrite using `[hπ.unitaryMass_eq, comap_toLev V K hπ]`. Both sides reduce to the same expression.
-/
theorem mass_eq_adelic : unitaryMass D.sp.cm.sig V.gram (toLev V K) = classMass (GQ V) (K.comap (finE V)) := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rw [hπ.unitaryMass_eq, comap_toLev V K hπ]
  rfl

/- English proof (translation)
Use `le_antisymm (fun g hg => ?_) (sup_le inf_le_right fun g hg => ?_)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `parts_spec D.sp.cm.sig V.gram`. Take `⟨k, k1, k2⟩` from `h2 1 (finHom V g)`. Establish `hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram` using `(h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩`. Set `k' : GA D V` to `⟨k, hk⟩`.

Establish `e : finHom V k' = finHom V g` using `k2`. Rewrite using `[← mul_inv_cancel_left k' g]`. Use `mul_mem (Subgroup.mem_sup_left ⟨k1, ?_⟩) (Subgroup.mem_sup_right ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `bc (swapAE D) (finHom V k') ∈ K`. Rewrite using `[e]`.

Conclude with `hg`. Express the relevant statement in the definitionally equal form `finHom V (k'⁻¹ * g) = 1`. Rewrite using `[map_mul, map_inv, e, inv_mul_cancel]`. Express the relevant statement in the definitionally equal form `bc (swapAE D) (finHom V g) ∈ K`. Rewrite using `[show finHom V g = 1 from hg, map_one]`.

Conclude with `one_mem _`.
-/
theorem comap_finE : K.comap (finE V) = levA V K ⊔ GinfC V := by
  refine le_antisymm (fun g hg => ?_) (sup_le inf_le_right fun g hg => ?_)
  · obtain ⟨h1, h2⟩ := parts_spec D.sp.cm.sig V.gram
    obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
    have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
      (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩
    let k' : GA D V := ⟨k, hk⟩
    have e : finHom V k' = finHom V g := k2
    rw [← mul_inv_cancel_left k' g]
    refine mul_mem (Subgroup.mem_sup_left ⟨k1, ?_⟩) (Subgroup.mem_sup_right ?_)
    · change bc (swapAE D) (finHom V k') ∈ K
      rw [e]
      exact hg
    · change finHom V (k'⁻¹ * g) = 1
      rw [map_mul, map_inv, e, inv_mul_cancel]
  · change bc (swapAE D) (finHom V g) ∈ K
    rw [show finHom V g = 1 from hg, map_one]
    exact one_mem _

variable {V K} in

/- English proof (translation)
Use `haveI : Nontrivial (Af D.host.F) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 D.host.F)`. Conclude with `(Formalism.UG.evalV D.host.F ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩).toRingHom.domain_nontrivial`. Use `haveI : Nontrivial (EAf D) := (Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := D.host.E) (B := Af D.host.F) (algebraMap D.host.F D.host.E).injective).nontrivial`. Establish `hm : ∀ γ : UR D.sp.cm V.gram, bc (inclE (F` using `D.host.F) (Af D.host.F)) γ.1 ∈ UA D.sp.cm V.gram := fun γ => Formalism.UG.Final.BCMem _ _ (Fin V.rank) (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.sigR D.sp.cm.sig (Af D.host.F)) (inclE (F := D.host.F) (Af D.host.F)) (RingHom.ext fun _ => rfl) V.gram γ.1 γ.2`.

Use `⟨Equiv.ofBijective (fun x => ⟨⟨⟨_, hm x.1⟩, x.1.1, x.1.2, rfl⟩, ?_⟩) ⟨fun x y e => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h : Formalism.L2.DIV.conjIn _ _ _ x.1 ∈ K` using `x.2`. Rewrite `h` using `[Formalism.L2.DIV.conjIn_apply]`. Conclude with `h`. Establish `e1` using `congrArg (fun z => z.1.1.1.1) e`.

Conclude with `Subtype.ext (Subtype.ext (Units.ext (Matrix.map_injective (inclE (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective e1)))`. Introduce and unpack `⟨⟨⟨g, hg⟩, u, hu, e⟩, h⟩`. Take `rfl : bc (inclE (F` from `D.host.F) (Af D.host.F)) u = g := e`. Use `⟨⟨⟨u, hu⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.L2.DIV.conjIn _ _ _ _ ∈ K`.

Rewrite using `[Formalism.L2.DIV.conjIn_apply]`. Conclude with `h`.
-/
theorem nonempty_gam_equiv (c : Cl D.sp.cm V.gram K) :
    Nonempty (Gam c ≃ stabAt (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) c.out) := by
  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (EAf D) :=
    (Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := D.host.E) (B := Af D.host.F)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hm : ∀ γ : UR D.sp.cm V.gram, bc (inclE (F := D.host.F) (Af D.host.F)) γ.1 ∈ UA D.sp.cm V.gram := fun γ =>
    Formalism.UG.Final.BCMem _ _ (Fin V.rank) (D.sp.cm.sig : D.host.E →+* D.host.E)
      (Formalism.UG.sigR D.sp.cm.sig (Af D.host.F)) (inclE (F := D.host.F) (Af D.host.F))
      (RingHom.ext fun _ => rfl) V.gram γ.1 γ.2
  refine ⟨Equiv.ofBijective (fun x => ⟨⟨⟨_, hm x.1⟩, x.1.1, x.1.2, rfl⟩, ?_⟩) ⟨fun x y e => ?_, ?_⟩⟩
  · have h : Formalism.L2.DIV.conjIn _ _ _ x.1 ∈ K := x.2
    rw [Formalism.L2.DIV.conjIn_apply] at h
    exact h
  · have e1 := congrArg (fun z => z.1.1.1.1) e
    exact Subtype.ext (Subtype.ext (Units.ext
      (Matrix.map_injective (inclE (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective e1)))
  · rintro ⟨⟨⟨g, hg⟩, u, hu, e⟩, h⟩
    obtain rfl : bc (inclE (F := D.host.F) (Af D.host.F)) u = g := e
    refine ⟨⟨⟨u, hu⟩, ?_⟩, rfl⟩
    change Formalism.L2.DIV.conjIn _ _ _ _ ∈ K
    rw [Formalism.L2.DIV.conjIn_apply]
    exact h

/- English proof (translation)
Conclude with `and_congr_right fun _ => ⟨fun h => finite_stabAt_of_out fun c => (nonempty_gam_equiv c).elim fun e => e.finite_iff.1 (h c), fun h c => (nonempty_gam_equiv c).elim fun e => e.finite_iff.2 (h _)⟩`.
-/
theorem classSumOK_iff : ClassSumOK V K ↔
    FiniteClasses (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) := by
  exact and_congr_right fun _ =>
    ⟨fun h => finite_stabAt_of_out fun c => (nonempty_gam_equiv c).elim fun e => e.finite_iff.1 (h c),
      fun h c => (nonempty_gam_equiv c).elim fun e => e.finite_iff.2 (h _)⟩

/- English proof (translation)
Rewrite using `[classSumOK_iff, toLev, finiteClasses_comap _ _ _ (swapPts (Af D.host.F) D.sp.cm.sig V.gram).surjective (swapPts (Af D.host.F) D.sp.cm.sig V.gram).injective.injOn, map_swapPts_rat]`.
-/
theorem classSumOK_iff_toLev : ClassSumOK V K ↔
    FiniteClasses (ratIn (Af D.host.F) D.sp.cm.sig V.gram) (toLev V K) := by
  rw [classSumOK_iff, toLev, finiteClasses_comap _ _ _ (swapPts (Af D.host.F) D.sp.cm.sig V.gram).surjective
    (swapPts (Af D.host.F) D.sp.cm.sig V.gram).injective.injOn, map_swapPts_rat]

/- English proof (translation)
Rewrite using `[mass_eq_fin, classMass_eq_finsum_out]`. Establish `key : ∀ {α : Type} (f g : α → ℕ), (∀ c, f c = g c) → ∑ᶠ c, ((f c : ℂ))⁻¹ * (1 * star 1) = ((∑ᶠ c, ((g c : ℝ))⁻¹ : ℝ) : ℂ)` using `fun f g h => Eq.trans (finsum_congr fun c => by simp [h c]) (AddMonoidHom.map_finsum_of_preimage_zero Complex.ofRealHom.toAddMonoidHom (fun x hx => by simpa using hx) _).symm`. Conclude with `key _ _ fun c => (nonempty_gam_equiv c).elim fun e => Nat.card_congr e`.
-/
theorem clSum_one : clSum V K (fun _ => 1) (fun _ => 1) = (unitaryMass D.sp.cm.sig V.gram (toLev V K) : ℂ) := by
  rw [mass_eq_fin, classMass_eq_finsum_out]
  have key : ∀ {α : Type} (f g : α → ℕ), (∀ c, f c = g c) →
      ∑ᶠ c, ((f c : ℂ))⁻¹ * (1 * star 1) = ((∑ᶠ c, ((g c : ℝ))⁻¹ : ℝ) : ℂ) := fun f g h =>
    Eq.trans (finsum_congr fun c => by simp [h c])
      (AddMonoidHom.map_finsum_of_preimage_zero Complex.ofRealHom.toAddMonoidHom
        (fun x hx => by simpa using hx) _).symm
  exact key _ _ fun c => (nonempty_gam_equiv c).elim fun e => Nat.card_congr e

variable {V K}

/- English proof (translation)
Take `⟨hσ, hJ⟩` from `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm`. Take `⟨-, ⟨θ, hθ⟩, h1⟩` from `hμ`. Take `⟨⟨A, hA⟩, h2⟩` from `h1 θ hθ`. Take `⟨⟨m, hm⟩, h3⟩` from `h2 A hA`. Establish `h4` using `h3 m hm (fun _ => Set.univ) fun _ => MeasurableSet.univ`.

Rewrite `h4` using `[Finset.prod_eq_one fun ρ _ => (hm ρ).2.measure_univ]`. Rewrite using `[← h4]`. Use `congr 1`. Use extensionality with `g`. Use `⟨fun hg => ⟨hg, fun ρ => ?_⟩, fun hg => hg.1⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `exists_upq_extends (A ρ) _ _ (hA ρ) (by`. Rewrite using `[gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 (hJ V).2) (GlobalTheory.Mem.VolExists.infMat_unitary V.gram hσ (hθ ρ) g)`. Conclude with `⟨b, trivial, hb⟩`.
-/
theorem measure_comap_finE {μ : Measure (GA D V)} (hμ : IsMeasLevDef V K μ) : μ (K.comap (finE V)) = 1 := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := hμ
  obtain ⟨⟨A, hA⟩, h2⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h3⟩ := h2 A hA
  have h4 := h3 m hm (fun _ => Set.univ) fun _ => MeasurableSet.univ
  rw [Finset.prod_eq_one fun ρ _ => (hm ρ).2.measure_univ] at h4
  rw [← h4]
  congr 1
  ext g
  refine ⟨fun hg => ⟨hg, fun ρ => ?_⟩, fun hg => hg.1⟩
  obtain ⟨b, hb⟩ := exists_upq_extends (A ρ) _ _ (hA ρ) (by
    rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (hJ V).2) (GlobalTheory.Mem.VolExists.infMat_unitary V.gram hσ (hθ ρ) g)
  exact ⟨b, trivial, hb⟩

/- English proof (translation)
The claim follows from `have h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm (classSumOK_iff_toLev V K).2 (finiteClasses_unitary h.1 (h.2 V) hd hc ho)`.
-/
theorem classSumOK_of_isTotDef (hd : IsTotDef D.sp.cm.sig V.gram)
    (hc : IsCompact (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)))
    (ho : IsOpen (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram))) : ClassSumOK V K :=
  have h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  (classSumOK_iff_toLev V K).2 (finiteClasses_unitary h.1 (h.2 V) hd hc ho)

/- English proof (translation)
The claim follows from `have h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm unitaryMass_pos h.1 (h.2 V) hd hc ho`.
-/
theorem mass_pos (hd : IsTotDef D.sp.cm.sig V.gram)
    (hc : IsCompact (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)))
    (ho : IsOpen (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram))) :
    0 < unitaryMass D.sp.cm.sig V.gram (toLev V K) :=
  have h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  unitaryMass_pos h.1 (h.2 V) hd hc ho

/- English proof (translation)
Establish `h` using `GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm`. Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Use `haveI := hμ.1`. Use `hπ.measure_toReal h.1 (h.2 V) hd hc ho μ ?_ h𝓕` and prove the remaining obligations. Rewrite using `[comap_toLev V K hπ]`.

Conclude with `measure_comap_finE hμ`.
-/
theorem measure_toReal_eq_mass (hd : IsTotDef D.sp.cm.sig V.gram)
    (hc : IsCompact (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)))
    (ho : IsOpen (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram))) {μ : Measure (GA D V)}
    (hμ : IsMeasLevDef V K μ) {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    (μ 𝓕).toReal = unitaryMass D.sp.cm.sig V.gram (toLev V K) := by
  have h := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  haveI := hμ.1
  refine hπ.measure_toReal h.1 (h.2 V) hd hc ho μ ?_ h𝓕
  rw [comap_toLev V K hπ]
  exact measure_comap_finE hμ

variable (V)

def latStab : Subgroup (HA (Af D.host.F) D.sp.cm.sig V.gram) :=
  GlobalTheory.Mem.Vol.StabGroup.stabGrp D.host.F D.sp.cm.sig V.gram (L0c D V)

def latLev : Subgroup (GL (Fin V.rank) (EAf D)) :=
  ((latStab V).map (swapPts (Af D.host.F) D.sp.cm.sig V.gram :
    HA (Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram)).map (UA D.sp.cm V.gram).subtype

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latStab (h : HA (Af D.host.F) D.sp.cm.sig V.gram) : h ∈ latStab V ↔
    ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (HA.mat (Af D.host.F) D.sp.cm.sig V.gram h).1 *ᵥ y ∈ latHat D.host.F D.host.E (L0c D V) := Iff.rfl

/- English proof (translation)
Rewrite using `[toLev, latLev, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), Subgroup.comap_map_eq_self_of_injective (swapPts (Af D.host.F) D.sp.cm.sig V.gram).injective]`.
-/
theorem toLev_latLev : toLev V (latLev V) = latStab V := by
  rw [toLev, latLev, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _),
    Subgroup.comap_map_eq_self_of_injective (swapPts (Af D.host.F) D.sp.cm.sig V.gram).injective]

/- English proof (translation)
Set `f` to `V.frame.equivFun.toLinearMap`. Set `L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)` to `V.L0.map (f.restrictScalars (𝓞 D.host.E))`. Establish `hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0`. Rewrite using `[V.frame.sum_equivFun]` and apply the resulting hypothesis. Introduce `hv`. Use `⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.equivFun_symm_apply]`. Conclude with `hv`. Establish `hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Take `⟨x, rfl⟩` from `V.frame.equivFun.surjective v`. Establish `hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V)`. Rewrite using `[V.standardTuple_isLattice.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Use `Submodule.mem_map_of_mem (f := f) hx` as an intermediate fact.

Rewrite `this` using `[Submodule.map_span]`. Conclude with `this`. Take `⟨S, hS, ho, hc⟩` from `GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab D.host.F D.host.E D.sp.cm.sig V.rank V.gram L (V.standardTuple_isLattice.fg.map _) hsp`. Rewrite `hS` using `[hL]`. Take `rfl : S = latStab V` from `Subgroup.ext hS`.

Conclude with `⟨hc, ho⟩`.
-/
theorem latStab_compact_open : IsCompact (latStab V : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) ∧
    IsOpen (latStab V : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  obtain ⟨S, hS, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab D.host.F D.host.E D.sp.cm.sig V.rank
    V.gram L (V.standardTuple_isLattice.fg.map _) hsp
  rw [hL] at hS
  obtain rfl : S = latStab V := Subgroup.ext hS
  exact ⟨hc, ho⟩

/- English proof (translation)
Use extensionality with `g`. Establish `e : (HA.mat (Af D.host.F) D.sp.cm.sig V.gram (π g)).1 = finMat D.sp.cm.sig V.gram g` using `congrArg Units.val (hπ g)`. Establish `e' : g ∈ (latStab V).comap π ↔ _` using `mem_latStab V (π g)`. Rewrite `e'` using `[e]`. Conclude with `⟨fun h => ⟨h.1, e'.1 h.2, fun v hv => absurd hv (Finset.notMem_empty v)⟩, fun h => ⟨h.1, e'.2 h.2.1⟩⟩`.
-/
theorem inf_comap_latStab {π : GA D V →* HA (Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) : (GfC V ⊓ (latStab V).comap π : Subgroup (GA D V)) = KsphC V ∅ := by
  ext g
  have e : (HA.mat (Af D.host.F) D.sp.cm.sig V.gram (π g)).1 = finMat D.sp.cm.sig V.gram g :=
    congrArg Units.val (hπ g)
  have e' : g ∈ (latStab V).comap π ↔ _ := mem_latStab V (π g)
  rw [e] at e'
  exact ⟨fun h => ⟨h.1, e'.1 h.2, fun v hv => absurd hv (Finset.notMem_empty v)⟩, fun h => ⟨h.1, e'.2 h.2.1⟩⟩

/- English proof (translation)
Take `⟨π, hπ, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Rewrite using `[← inf_comap_latStab V hπ, levA, ← comap_toLev V _ hπ, toLev_latLev]`.
-/
theorem levA_latLev : (levA V (latLev V) : Set (GA D V)) = KsphC V ∅ := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rw [← inf_comap_latStab V hπ, levA, ← comap_toLev V _ hπ, toLev_latLev]

/- English proof (translation)
Rewrite `hS` using `[← inf_comap_latStab V hπ, SetLike.coe_set_eq]`. Use extensionality with `b`. Take `⟨h1, h2⟩` from `parts_spec D.sp.cm.sig V.gram`. Take `⟨k, k1, k2⟩` from `h2 1 (HA.mat (Af D.host.F) D.sp.cm.sig V.gram b)`. Set `k' : GA D V` to `⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩`.

Establish `hk : k' ∈ GfC V` using `k1`. Establish `e : π k' = b` using `Subtype.ext ((hπ _).trans k2)`. Use `SetLike.ext_iff.1 hS k'` as an intermediate fact. Rewrite using `[← e]`. Conclude with `⟨fun h => (this.1 ⟨hk, h⟩).2, fun h => (this.2 ⟨hk, h⟩).2⟩`.
-/
theorem eq_latStab {π : GA D V →* HA (Af D.host.F) D.sp.cm.sig V.gram} (hπ : IsFinProj D.sp.cm.sig V.gram π)
    {S : Subgroup (HA (Af D.host.F) D.sp.cm.sig V.gram)}
    (hS : (GfC V ⊓ S.comap π : Subgroup (GA D V)) = KsphC V ∅) : S = latStab V := by
  rw [← inf_comap_latStab V hπ, SetLike.coe_set_eq] at hS
  ext b
  obtain ⟨h1, h2⟩ := parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (HA.mat (Af D.host.F) D.sp.cm.sig V.gram b)
  let k' : GA D V := ⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩
  have hk : k' ∈ GfC V := k1
  have e : π k' = b := Subtype.ext ((hπ _).trans k2)
  have := SetLike.ext_iff.1 hS k'
  rw [← e]
  exact ⟨fun h => (this.1 ⟨hk, h⟩).2, fun h => (this.2 ⟨hk, h⟩).2⟩

/- English proof (translation)
Take `⟨hc, ho⟩` from `latStab_compact_open V`. Use `⟨fun K => ⟨mass_eq_fin V K, mass_eq_adelic V K, comap_finE V K, clSum_one V K, classSumOK_iff V K, fun hd hc ho => ⟨classSumOK_of_isTotDef hd hc ho, mass_pos hd hc ho, fun _ _ hμ h𝓕 => measure_toReal_eq_mass hd hc ho hμ h𝓕⟩⟩, toLev_latLev V, levA_latLev V, fun π hπ S => ⟨eq_latSt …` and prove the remaining obligations. Rewrite `hc`, `ho`, the goal using `[← toLev_latLev]`. Establish `h` using `classSumOK_of_isTotDef hd hc ho`. Conclude with `⟨h, (classSumOK_iff_toLev V _).1 h, mass_pos hd hc ho⟩`.
-/
theorem mass_levels (D : D7) (V : HSp D) :
    (∀ K : Subgroup (GL (Fin V.rank) (EAf D)),
      unitaryMass D.sp.cm.sig V.gram (toLev V K) =
        classMass (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) ∧
      unitaryMass D.sp.cm.sig V.gram (toLev V K) = classMass (GQ V) (K.comap (finE V)) ∧
      K.comap (finE V) = levA V K ⊔ GinfC V ∧
      clSum V K (fun _ => 1) (fun _ => 1) = (unitaryMass D.sp.cm.sig V.gram (toLev V K) : ℂ) ∧
      (ClassSumOK V K ↔ FiniteClasses (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram))) ∧
      (IsTotDef D.sp.cm.sig V.gram → IsCompact (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) →
        IsOpen (toLev V K : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) →
        ClassSumOK V K ∧ 0 < unitaryMass D.sp.cm.sig V.gram (toLev V K) ∧
        ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsMeasLevDef V K μ → IsFundamentalDomain (GQ V) 𝓕 μ →
          (μ 𝓕).toReal = unitaryMass D.sp.cm.sig V.gram (toLev V K))) ∧
    toLev V (latLev V) = latStab V ∧ (levA V (latLev V) : Set (GA D V)) = KsphC V ∅ ∧
    (∀ π : GA D V →* HA (Af D.host.F) D.sp.cm.sig V.gram, IsFinProj D.sp.cm.sig V.gram π →
      ∀ S : Subgroup (HA (Af D.host.F) D.sp.cm.sig V.gram),
        ((GfC V ⊓ S.comap π : Subgroup (GA D V)) : Set (GA D V)) = KsphC V ∅ ↔ S = latStab V) ∧
    IsCompact (latStab V : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) ∧
    IsOpen (latStab V : Set (HA (Af D.host.F) D.sp.cm.sig V.gram)) ∧
    (IsTotDef D.sp.cm.sig V.gram → ClassSumOK V (latLev V) ∧
      FiniteClasses (ratIn (Af D.host.F) D.sp.cm.sig V.gram) (latStab V) ∧
      0 < unitaryMass D.sp.cm.sig V.gram (latStab V)) := by
  obtain ⟨hc, ho⟩ := latStab_compact_open V
  refine ⟨fun K => ⟨mass_eq_fin V K, mass_eq_adelic V K, comap_finE V K, clSum_one V K, classSumOK_iff V K,
    fun hd hc ho => ⟨classSumOK_of_isTotDef hd hc ho, mass_pos hd hc ho,
      fun _ _ hμ h𝓕 => measure_toReal_eq_mass hd hc ho hμ h𝓕⟩⟩, toLev_latLev V, levA_latLev V,
    fun π hπ S => ⟨eq_latStab V hπ, fun h => h ▸ inf_comap_latStab V hπ⟩, hc, ho, fun hd => ?_⟩
  rw [← toLev_latLev] at hc ho ⊢
  have h := classSumOK_of_isTotDef hd hc ho
  exact ⟨h, (classSumOK_iff_toLev V _).1 h, mass_pos hd hc ho⟩

end GlobalTheory.Mass.Levels
