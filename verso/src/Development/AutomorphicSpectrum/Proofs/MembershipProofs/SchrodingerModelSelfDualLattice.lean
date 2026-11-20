import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CosetMod

/- English proof (translation)
Establish `hcoset : ∀ a b : G, (a : G ⧸ H) = b → χ a = χ b`. Introduce `a b hab`. Establish `hmem : -a + b ∈ H` using `QuotientAddGroup.eq.mp hab`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations.

Simplify using `[h]`. Use `push_neg at h`. Take `⟨g, hg⟩` from `h`. Establish `hshift : ∀ q : G ⧸ H, χ g * χ q.out = χ ((QuotientAddGroup.mk g + q).out)`. Introduce `q`.

Rewrite using `[← AddChar.map_add_eq_mul]`. Apply `hcoset` to reduce the goal to its premises. Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']`. Establish `key : χ g * ∑ q : G ⧸ H, χ q.out = ∑ q : G ⧸ H, χ q.out`. Rewrite using `[Finset.mul_sum]`.

Repeatedly rewrite using `[hshift]`. Conclude with `Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk g)) _ _ (fun q => rfl)`. Establish `h0 : (χ g - 1) * ∑ q : G ⧸ H, χ q.out = 0` using `by rw [sub_mul, key, one_mul, sub_self]`. Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h1) hg`.

Conclude with `h1`.
-/
theorem sum_out {G : Type} [AddCommGroup G] (H : AddSubgroup G) [Fintype (G ⧸ H)] (χ : AddChar G ℂ)
    (hχ : ∀ h ∈ H, χ h = 1) :
    ((∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = Fintype.card (G ⧸ H)) ∧
      (¬ (∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = 0) := by
  have hcoset : ∀ a b : G, (a : G ⧸ H) = b → χ a = χ b := by
    intro a b hab
    have hmem : -a + b ∈ H := QuotientAddGroup.eq.mp hab
    calc χ a = χ a * χ (-a + b) := by rw [hχ _ hmem, mul_one]
      _ = χ b := by rw [← AddChar.map_add_eq_mul, add_neg_cancel_left]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [h]
  · push_neg at h
    obtain ⟨g, hg⟩ := h
    have hshift : ∀ q : G ⧸ H, χ g * χ q.out = χ ((QuotientAddGroup.mk g + q).out) := by
      intro q
      rw [← AddChar.map_add_eq_mul]
      apply hcoset
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    have key : χ g * ∑ q : G ⧸ H, χ q.out = ∑ q : G ⧸ H, χ q.out := by
      rw [Finset.mul_sum]
      simp_rw [hshift]
      exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk g)) _ _ (fun q => rfl)
    have h0 : (χ g - 1) * ∑ q : G ⧸ H, χ q.out = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hg
    · exact h1

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s (fun _ => by simp) ?_` and prove the remaining obligations. Introduce `a s ha ih h`. Rewrite using `[Finset.sum_insert ha, AddChar.map_add_eq_mul, h a (Finset.mem_insert_self a s), ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]`.
-/
private theorem addChar_sum_eq_one_of_forall {R ι : Type} [CommRing R] (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, ψ (f i) = 1) : ψ (∑ i ∈ s, f i) = 1 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, h a (Finset.mem_insert_self a s),
    ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]

/- English proof (translation)
Introduce `R _ _ _ _ _ _ ψ O u κ _ v hG hv`. Set `L : AddSubgroup (κ → R)` to `AddSubgroup.pi Set.univ (fun _ => O.toAddSubgroup)`. Establish `memL : ∀ y : κ → R, y ∈ L ↔ ∀ i, y i ∈ O`. Introduce `y`. Simplify using `[L, AddSubgroup.mem_pi]`.

Set `Gs : AddSubgroup (κ → R)` to `L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ * v : Rˣ)) : R))`. Set `Hs : AddSubgroup (κ → R)` to `L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ : Rˣ)) : R))`. Establish `memG : ∀ y : κ → R, y ∈ Gs ↔ ∀ i, (((u⁻¹ * v : Rˣ)) : R) * y i ∈ O`. Introduce `y`. Simplify using `only [Gs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL, Pi.smul_apply, smul_eq_mul]`.

Establish `memH : ∀ y : κ → R, y ∈ Hs ↔ ∀ i, (((u⁻¹ : Rˣ)) : R) * y i ∈ O`. Introduce `y`. Simplify using `only [Hs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL, Pi.smul_apply, smul_eq_mul]`. Establish `hLset : (L : Set (κ → R)) = Set.univ.pi (fun _ => (O : Set R))`. Use extensionality with `y`.

Simplify using `[memL]`. Establish `hLopen : IsOpen (L : Set (κ → R))`. Rewrite using `[hLset]`. Conclude with `isOpen_set_pi Set.finite_univ (fun _ _ => hG.isOpen)`. Establish `hLcpt : IsCompact (L : Set (κ → R))`.

Rewrite using `[hLset]`. Conclude with `isCompact_univ_pi (fun _ => hG.compact)`. Establish `hGset : (Gs : Set (κ → R)) = (fun y : κ → R => ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • y) '' (L : Set (κ → R))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Use `⟨(((u⁻¹ * v : Rˣ)) : R) • y, hy, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_smul, Units.inv_mul, one_smul]`. Introduce and unpack `⟨z, hz, rfl⟩ show (((u⁻¹ * v : Rˣ)) : R) • ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • z ∈ L`. Rewrite using `[smul_smul, Units.mul_inv, one_smul]`.

Conclude with `hz`. Establish `hGcpt : IsCompact (Gs : Set (κ → R))`. Rewrite using `[hGset]`. Conclude with `hLcpt.image (continuous_const_smul _)`. Establish `hHopen : IsOpen (Hs : Set (κ → R))` using `hLopen.preimage (continuous_const_smul (((u⁻¹ : Rˣ)) : R))`.

Set `H : AddSubgroup Gs` to `Hs.addSubgroupOf Gs`. Establish `hHopen' : IsOpen (H : Set Gs)` using `hHopen.preimage continuous_subtype_val`. Use `haveI : CompactSpace Gs := isCompact_iff_compactSpace.mp hGcpt`. Use `haveI : Finite (Gs ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHopen'`. Use `letI : Fintype (Gs ⧸ H) := Fintype.ofFinite _`.

Establish `hfun : (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) = ∑ q : Gs ⧸ H, ((Fintype.card (Gs ⧸ H) : ℂ)⁻¹) • schr ψ (0, ((q.out : Gs) : κ → R)) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero]`. Distinguish the cases in `hx : ∀ i, x i ∈ O`.

Set `χx : AddChar Gs ℂ` to `{ toFun := fun y => ψ (x ⬝ᵥ (y : κ → R)) map_zero_eq_one' := by simp map_add_eq_mul' := by intro a b; simp [dotProduct_add, AddChar.map_add_eq_mul] }`. Establish `hχ : ∀ h ∈ H, χx h = 1`. Introduce `h hh`. Establish `hh' : ((h : Gs) : κ → R) ∈ Hs` using `AddSubgroup.mem_addSubgroupOf.mp hh`. Use `show ψ (x ⬝ᵥ ((h : Gs) : κ → R)) = 1`.

Apply `addChar_sum_eq_one_of_forall` to reduce the goal to its premises. Introduce `i _`. Establish `h1` using `(hG.ann _).mpr ((memH _).mp hh' i) (x i) (hx i)`. Rewrite `h1` using `[mul_comm]`. Then use the resulting hypothesis. Take `⟨hA, hB⟩` from `sum_out H χx hχ`.

Establish `hrw : ∀ q : Gs ⧸ H, (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ * (ψ (x ⬝ᵥ ((q.out : Gs) : κ → R)) * Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) x) = (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ * χx q.out`. Introduce `q`. Simplify using `only [Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_one]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl (fun q _ => hrw q), ← Finset.mul_sum]`.

Distinguish the cases in `hs : ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O`. Establish `htriv : ∀ g, χx g = 1`. Introduce `g`. Use `show ψ (x ⬝ᵥ ((g : Gs) : κ → R)) = 1`. Apply `addChar_sum_eq_one_of_forall` to reduce the goal to its premises.

Introduce `i _`. Establish `hg` using `(memG _).mp g.2 i`. Establish `hz : ((u⁻¹ : Rˣ) : R) * ((v : R) * (g : κ → R) i) ∈ O`. Rewrite using `[← mul_assoc, ← Units.val_mul]`. Conclude with `hg`.

Establish `h1` using `(hG.ann _).mpr hz _ (hs i)`. Establish `e : (v : R) * (g : κ → R) i * (((v⁻¹ : Rˣ) : R) * x i) = x i * (g : κ → R) i`. Rewrite using `[mul_comm (v : R) ((g : κ → R) i), mul_assoc, Units.mul_inv_cancel_left, mul_comm]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Rewrite using `[hA htriv, Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]`.

Conclude with `(inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm`. Establish `hnt : ¬ ∀ g, χx g = 1` using `by push_neg at hs`. Take `⟨i, hi⟩` from `hs`. Establish `hz : ¬ ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) ∈ O`. Establish `e : ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) = ((v⁻¹ : Rˣ) : R) * x i`.

Rewrite using `[mul_comm (((v⁻¹ : Rˣ) : R)) (u : R), mul_assoc (u : R), Units.inv_mul_cancel_left]`. Rewrite using `[e]`. Conclude with `hi`. Rewrite `hz` using `[← hG.ann]`. Use `push_neg at hz`.

Take `⟨y, hy, hψ⟩` from `hz`. Introduce `hall`. Establish `hmem : (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) ∈ Gs`. Rewrite using `[memG]`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Pi.single_eq_same]`. Establish `e : (((u⁻¹ * v : Rˣ)) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * y) = y`. Rewrite using `[Units.val_mul, mul_assoc, ← mul_assoc (v : R), ← mul_assoc (v : R), Units.mul_inv, one_mul, Units.inv_mul_cancel_left]`.

Rewrite using `[e]`. Conclude with `hy`. Simplify using `only [Pi.single_eq_of_ne hj, mul_zero]`. Conclude with `O.zero_mem`. Establish `h1` using `hall ⟨_, hmem⟩`.

Apply `hψ` to reduce the goal to its premises. Establish `e2 : x ⬝ᵥ (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) = ((v⁻¹ : Rˣ) : R) * (u : R) * x i * y`. Rewrite using `[dotProduct_single]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e2]`.

Conclude with `h1`. Rewrite using `[hB hnt, mul_zero, Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]`. Establish `hs : ¬ ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Introduce `i`. Use `O.mul_mem hv (h i)` as an intermediate fact. Rewrite `this` using `[Units.mul_inv_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_zero, mul_zero]`. Rewrite using `[hfun]`. Conclude with `Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))`.
-/
theorem indicator_mem_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  intro R _ _ _ _ _ _ ψ O u κ _ v hG hv
  classical
  let L : AddSubgroup (κ → R) := AddSubgroup.pi Set.univ (fun _ => O.toAddSubgroup)
  have memL : ∀ y : κ → R, y ∈ L ↔ ∀ i, y i ∈ O := by
    intro y; simp [L, AddSubgroup.mem_pi]
  let Gs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ * v : Rˣ)) : R))
  let Hs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ : Rˣ)) : R))
  have memG : ∀ y : κ → R, y ∈ Gs ↔ ∀ i, (((u⁻¹ * v : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Gs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have memH : ∀ y : κ → R, y ∈ Hs ↔ ∀ i, (((u⁻¹ : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Hs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have hLset : (L : Set (κ → R)) = Set.univ.pi (fun _ => (O : Set R)) := by
    ext y; simp [memL]
  have hLopen : IsOpen (L : Set (κ → R)) := by
    rw [hLset]; exact isOpen_set_pi Set.finite_univ (fun _ _ => hG.isOpen)
  have hLcpt : IsCompact (L : Set (κ → R)) := by
    rw [hLset]; exact isCompact_univ_pi (fun _ => hG.compact)
  have hGset : (Gs : Set (κ → R)) =
      (fun y : κ → R => ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • y) '' (L : Set (κ → R)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(((u⁻¹ * v : Rˣ)) : R) • y, hy, ?_⟩
      simp only [smul_smul, Units.inv_mul, one_smul]
    · rintro ⟨z, hz, rfl⟩
      show (((u⁻¹ * v : Rˣ)) : R) • ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • z ∈ L
      rw [smul_smul, Units.mul_inv, one_smul]; exact hz
  have hGcpt : IsCompact (Gs : Set (κ → R)) := by
    rw [hGset]; exact hLcpt.image (continuous_const_smul _)
  have hHopen : IsOpen (Hs : Set (κ → R)) :=
    hLopen.preimage (continuous_const_smul (((u⁻¹ : Rˣ)) : R))
  let H : AddSubgroup Gs := Hs.addSubgroupOf Gs
  have hHopen' : IsOpen (H : Set Gs) := hHopen.preimage continuous_subtype_val
  haveI : CompactSpace Gs := isCompact_iff_compactSpace.mp hGcpt
  haveI : Finite (Gs ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHopen'
  letI : Fintype (Gs ⧸ H) := Fintype.ofFinite _
  have hfun : (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) =
      ∑ q : Gs ⧸ H, ((Fintype.card (Gs ⧸ H) : ℂ)⁻¹) •
        schr ψ (0, ((q.out : Gs) : κ → R)) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero]
    by_cases hx : ∀ i, x i ∈ O
    · let χx : AddChar Gs ℂ :=
        { toFun := fun y => ψ (x ⬝ᵥ (y : κ → R))
          map_zero_eq_one' := by simp
          map_add_eq_mul' := by intro a b; simp [dotProduct_add, AddChar.map_add_eq_mul] }
      have hχ : ∀ h ∈ H, χx h = 1 := by
        intro h hh
        have hh' : ((h : Gs) : κ → R) ∈ Hs := AddSubgroup.mem_addSubgroupOf.mp hh
        show ψ (x ⬝ᵥ ((h : Gs) : κ → R)) = 1
        apply addChar_sum_eq_one_of_forall
        intro i _
        have h1 := (hG.ann _).mpr ((memH _).mp hh' i) (x i) (hx i)
        rwa [mul_comm] at h1
      obtain ⟨hA, hB⟩ := sum_out H χx hχ
      have hrw : ∀ q : Gs ⧸ H, (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ *
          (ψ (x ⬝ᵥ ((q.out : Gs) : κ → R)) *
            Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) x) =
          (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ * χx q.out := by
        intro q
        simp only [Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_one]
        rfl
      rw [Finset.sum_congr rfl (fun q _ => hrw q), ← Finset.mul_sum]
      by_cases hs : ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O
      · have htriv : ∀ g, χx g = 1 := by
          intro g
          show ψ (x ⬝ᵥ ((g : Gs) : κ → R)) = 1
          apply addChar_sum_eq_one_of_forall
          intro i _
          have hg := (memG _).mp g.2 i
          have hz : ((u⁻¹ : Rˣ) : R) * ((v : R) * (g : κ → R) i) ∈ O := by
            rw [← mul_assoc, ← Units.val_mul]; exact hg
          have h1 := (hG.ann _).mpr hz _ (hs i)
          have e : (v : R) * (g : κ → R) i * (((v⁻¹ : Rˣ) : R) * x i) = x i * (g : κ → R) i := by
            rw [mul_comm (v : R) ((g : κ → R) i), mul_assoc, Units.mul_inv_cancel_left, mul_comm]
          rwa [e] at h1
        rw [hA htriv, Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
        exact (inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm
      · have hnt : ¬ ∀ g, χx g = 1 := by
          push_neg at hs
          obtain ⟨i, hi⟩ := hs
          have hz : ¬ ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) ∈ O := by
            have e : ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) = ((v⁻¹ : Rˣ) : R) * x i := by
              rw [mul_comm (((v⁻¹ : Rˣ) : R)) (u : R), mul_assoc (u : R), Units.inv_mul_cancel_left]
            rw [e]; exact hi
          rw [← hG.ann] at hz
          push_neg at hz
          obtain ⟨y, hy, hψ⟩ := hz
          intro hall
          have hmem : (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) ∈ Gs := by
            rw [memG]
            intro j
            by_cases hj : j = i
            · subst hj
              simp only [Pi.single_eq_same]
              have e : (((u⁻¹ * v : Rˣ)) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * y) = y := by
                rw [Units.val_mul, mul_assoc, ← mul_assoc (v : R), ← mul_assoc (v : R),
                  Units.mul_inv, one_mul, Units.inv_mul_cancel_left]
              rw [e]; exact hy
            · simp only [Pi.single_eq_of_ne hj, mul_zero]; exact O.zero_mem
          have h1 := hall ⟨_, hmem⟩
          apply hψ
          have e2 : x ⬝ᵥ (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) =
              ((v⁻¹ : Rˣ) : R) * (u : R) * x i * y := by
            rw [dotProduct_single]; ring
          rw [← e2]; exact h1
        rw [hB hnt, mul_zero, Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
    · have hs : ¬ ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O := by
        intro h
        apply hx
        intro i
        have := O.mul_mem hv (h i)
        rwa [Units.mul_inv_cancel_left] at this
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_zero, mul_zero]
  rw [hfun]
  exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

end GlobalTheory.CompanionTheory.CosetMod
