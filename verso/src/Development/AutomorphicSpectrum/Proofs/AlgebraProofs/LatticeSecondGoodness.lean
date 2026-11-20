import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummandStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeFibreIdealLocallyFreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeGraphComapLocallyFreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeKernelLocallyFreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeBaseChangeFreeStatement

open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

/- English proof (translation)
Take `⟨-, k, f, c, hf, hc, hsum, hb⟩` from `hL`. Use `⟨fun a ha e he => SpanExact.smul_mem_spanOver RC _ ha he, k, fun l => algebraMap Ω C (f l), fun l => algebraMap Ω C (c l), fun l => hRC _ (hf l), fun l => hRC _ (hc l), ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (algebraMap Ω C) hsum`. Simplify `h` using `only [map_sum, map_mul, map_one]`. Take `⟨b, hli, hsp, hiff⟩` from `hb l`.

Establish `hbc` using `isBaseChange_bcMap Ω C ι`. Set `B : Module.Basis (Fin r) Ω (ι → Ω)` to `Module.Basis.mk hli hsp.ge`. Set `B'` to `hbc.basis B`. Establish `hB' : (⇑B' : Fin r → ι → C) = fun q => bcMap Ω C ι (b q)`. Use function extensionality and compare the values at `q`.

Simplify using `[B', B, IsBaseChange.basis_apply, Module.Basis.mk_apply]`. Establish `hbl : ∀ q, ∃ m : ℕ, f l ^ m • b q ∈ L` using `fun q => (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by`. Break down `eq_or_ne q' q with rfl | h` into its components or cases. Simplify using `[one_mem]`. Simplify using `[Pi.single_apply, h]⟩, by simp [Pi.single_apply]⟩`.

Use `⟨fun q => bcMap Ω C ι (b q), by rw [← hB']; exact B'.linearIndependent, by rw [← hB']; exact B'.span_eq, fun e => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Distinguish the cases in `hg : f l = 0`. Establish `hg' : algebraMap Ω C (f l) = 0` using `by rw [hg, map_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `_`. Use `⟨B'.repr e, fun q => ⟨1, by rw [hg', pow_one, zero_mul]; exact zero_mem _⟩, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← B'.sum_repr e]`. Rewrite using `[hB']`. Introduce `_`.

Conclude with `⟨1, by rw [hg', pow_one, zero_smul]; exact zero_mem _⟩`. Establish `hg' : algebraMap Ω C (f l) ≠ 0` using `(map_ne_zero _).2 hg`. Establish `hgR : algebraMap Ω C (f l) ∈ RC` using `hRC _ (hf l)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`.

Establish `key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))), ∃ a : Fin r → C, (∀ q, ∃ n : ℕ, algebraMap Ω C (f l) ^ n * a q ∈ RC) ∧ x = ∑ q, a q • bcMap Ω C ι (b q)`. Introduce `x hx`. Unfold `spanOver at hx`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, y, ⟨v, hv, rfl⟩, rfl⟩` from `hx`. Take `⟨av, hav, rfl⟩` from `(hiff v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩`. Use `⟨fun q => a * algebraMap Ω C (av q), fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hav q`. Conclude with `⟨n, by rw [mul_left_comm, ← map_pow, ← map_mul]; exact mul_mem ha (hRC _ hn)⟩`.

Simplify using `only [map_sum, map_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C (av q), smul_smul]`. Consider the case `zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨a', ha', rfl⟩` from `hy`. Use `⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`. Take `⟨n', hn'⟩` from `ha' q`.

Use `⟨n + n', ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap Ω C (f l) ^ (n + n') * (a + a') q = algebraMap Ω C (f l) ^ n' * (algebraMap Ω C (f l) ^ n * a q) + algebraMap Ω C (f l) ^ n * (algebraMap Ω C (f l) ^ n' * a' q)`. Rewrite using `[Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `add_mem (mul_mem (pow_mem hgR _) hn) (mul_mem (pow_mem hgR _) hn')`. Consider the case `neg x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Use `⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`.

Conclude with `⟨n, by rw [Pi.neg_apply, mul_neg]; exact neg_mem hn⟩`. Take `⟨a, ha, hae⟩` from `key _ hm`. Use `⟨fun q => (algebraMap Ω C (f l) ^ m)⁻¹ * a q, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_add, mul_assoc, ← mul_assoc (algebraMap Ω C (f l) ^ m), mul_inv_cancel₀ (pow_ne_zero _ hg'), one_mul]`. Conclude with `hn`. Establish `he : e = (algebraMap Ω C (f l) ^ m)⁻¹ • (algebraMap Ω C (f l) ^ m • e)`. Rewrite using `[smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg'), one_smul]`. Rewrite using `[he, hae, Finset.smul_sum]`.

Simplify using `only [smul_smul]`. Introduce and unpack `⟨a, ha, rfl⟩ choose na hna using ha choose mb hmb using hbl`. Use `⟨∑ q, na q + ∑ q, mb q, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun q _ => ?_` and prove the remaining obligations.

Establish `h1 : na q ≤ ∑ q, na q` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)`. Establish `h2 : mb q ≤ ∑ q, mb q` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)`. Establish `e1 : algebraMap Ω C (f l) ^ (∑ q, na q + ∑ q, mb q) = algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ na q * (algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * algebraMap Ω C (f l) ^ mb q)`. Rewrite using `[← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]`. Establish `hcoef : algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q) ∈ RC` using `mul_mem (mul_mem (pow_mem hgR _) (pow_mem hgR _)) (hna q)`.

Establish `hmem : (algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q)) • bcMap Ω C ι (f l ^ mb q • b q) ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω)))` using `AddSubgroup.subset_closure ⟨_, hcoef, _, ⟨_, hmb q, rfl⟩, rfl⟩`. Use `hmem using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_smul, ← algebraMap_smul C (f l ^ mb q), smul_smul, smul_smul, map_pow, e1]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem loc_free_base_change {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω]
    [Algebra o C] [Algebra Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C)
    (hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC) {ι : Type} [Finite ι] {r : ℕ}
    {L : AddSubgroup (ι → Ω)} (hL : LocFree R r L) :
    LocFree RC r (spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω)))) := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := hL
  refine ⟨fun a ha e he => SpanExact.smul_mem_spanOver RC _ ha he, k,
    fun l => algebraMap Ω C (f l), fun l => algebraMap Ω C (c l), fun l => hRC _ (hf l),
    fun l => hRC _ (hc l), ?_, fun l => ?_⟩
  · have h := congrArg (algebraMap Ω C) hsum
    simpa only [map_sum, map_mul, map_one] using h
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  have hbc := isBaseChange_bcMap Ω C ι
  let B : Module.Basis (Fin r) Ω (ι → Ω) := Module.Basis.mk hli hsp.ge
  let B' := hbc.basis B
  have hB' : (⇑B' : Fin r → ι → C) = fun q => bcMap Ω C ι (b q) := by
    funext q
    simp [B', B, IsBaseChange.basis_apply, Module.Basis.mk_apply]
  have hbl : ∀ q, ∃ m : ℕ, f l ^ m • b q ∈ L := fun q =>
    (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      rcases eq_or_ne q' q with rfl | h
      · simp [one_mem]
      · simp [Pi.single_apply, h]⟩, by simp [Pi.single_apply]⟩
  refine ⟨fun q => bcMap Ω C ι (b q), by rw [← hB']; exact B'.linearIndependent,
    by rw [← hB']; exact B'.span_eq, fun e => ?_⟩
  beta_reduce
  by_cases hg : f l = 0
  · have hg' : algebraMap Ω C (f l) = 0 := by rw [hg, map_zero]
    constructor
    · intro _
      refine ⟨B'.repr e, fun q => ⟨1, by rw [hg', pow_one, zero_mul]; exact zero_mem _⟩, ?_⟩
      conv_lhs => rw [← B'.sum_repr e]
      rw [hB']
    · intro _
      exact ⟨1, by rw [hg', pow_one, zero_smul]; exact zero_mem _⟩
  have hg' : algebraMap Ω C (f l) ≠ 0 := (map_ne_zero _).2 hg
  have hgR : algebraMap Ω C (f l) ∈ RC := hRC _ (hf l)
  constructor
  · rintro ⟨m, hm⟩
    have key : ∀ x ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))), ∃ a : Fin r → C,
        (∀ q, ∃ n : ℕ, algebraMap Ω C (f l) ^ n * a q ∈ RC) ∧
          x = ∑ q, a q • bcMap Ω C ι (b q) := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, y, ⟨v, hv, rfl⟩, rfl⟩ := hx
        obtain ⟨av, hav, rfl⟩ := (hiff v).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
        refine ⟨fun q => a * algebraMap Ω C (av q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := hav q
          exact ⟨n, by rw [mul_left_comm, ← map_pow, ← map_mul]; exact mul_mem ha (hRC _ hn)⟩
        · simp only [map_sum, map_smul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← algebraMap_smul C (av q), smul_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        refine ⟨a + a', fun q => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        obtain ⟨n', hn'⟩ := ha' q
        refine ⟨n + n', ?_⟩
        have h2 : algebraMap Ω C (f l) ^ (n + n') * (a + a') q =
            algebraMap Ω C (f l) ^ n' * (algebraMap Ω C (f l) ^ n * a q) +
              algebraMap Ω C (f l) ^ n * (algebraMap Ω C (f l) ^ n' * a' q) := by
          rw [Pi.add_apply]; ring
        rw [h2]
        exact add_mem (mul_mem (pow_mem hgR _) hn) (mul_mem (pow_mem hgR _) hn')
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by rw [Pi.neg_apply, mul_neg]; exact neg_mem hn⟩
    obtain ⟨a, ha, hae⟩ := key _ hm
    refine ⟨fun q => (algebraMap Ω C (f l) ^ m)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨n, hn⟩ := ha q
      refine ⟨n + m, ?_⟩
      rw [pow_add, mul_assoc, ← mul_assoc (algebraMap Ω C (f l) ^ m),
        mul_inv_cancel₀ (pow_ne_zero _ hg'), one_mul]
      exact hn
    · have he : e = (algebraMap Ω C (f l) ^ m)⁻¹ • (algebraMap Ω C (f l) ^ m • e) := by
        rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg'), one_smul]
      rw [he, hae, Finset.smul_sum]
      simp only [smul_smul]
  · rintro ⟨a, ha, rfl⟩
    choose na hna using ha
    choose mb hmb using hbl
    refine ⟨∑ q, na q + ∑ q, mb q, ?_⟩
    rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun q _ => ?_
    have h1 : na q ≤ ∑ q, na q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have h2 : mb q ≤ ∑ q, mb q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have e1 : algebraMap Ω C (f l) ^ (∑ q, na q + ∑ q, mb q) =
        algebraMap Ω C (f l) ^ (∑ q, na q - na q) * algebraMap Ω C (f l) ^ na q *
          (algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * algebraMap Ω C (f l) ^ mb q) := by
      rw [← pow_add, ← pow_add, ← pow_add, Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    have hcoef : algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q) ∈ RC :=
      mul_mem (mul_mem (pow_mem hgR _) (pow_mem hgR _)) (hna q)
    have hmem : (algebraMap Ω C (f l) ^ (∑ q, na q - na q) *
        algebraMap Ω C (f l) ^ (∑ q, mb q - mb q) * (algebraMap Ω C (f l) ^ na q * a q)) •
          bcMap Ω C ι (f l ^ mb q • b q) ∈ spanOver RC (bcMap Ω C ι '' (L : Set (ι → Ω))) :=
      AddSubgroup.subset_closure ⟨_, hcoef, _, ⟨_, hmb q, rfl⟩, rfl⟩
    convert hmem using 1
    rw [map_smul, ← algebraMap_smul C (f l ^ mb q), smul_smul, smul_smul, map_pow, e1]
    congr 1
    ring

/- English proof (translation)
Introduce `o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG1 hG2 haf`. Take `⟨hdL, hdB⟩` from `GlobalTheory.T.character_lattice_fibre_ideal_locally_free D R p w χ hc hB hG1 hG2`. Take `⟨hsL, hsB⟩` from `GlobalTheory.T.character_lattice_graph_comap_locally_free D R p w χ hc hB hG1 hG2`. Establish `hkL` using `GlobalTheory.T.character_lattice_kernel_locally_free D R p w χ hc hB hG1 hG2 haf`. Establish `h68` using `GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG1`.

Use `⟨fun τ => ⟨hkL τ, fun i => ⟨hdL τ i, hsL τ i⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `C _ _ _ _ RC hRC`. Establish `hbc` using `h68.2 C RC hRC`. Establish `h69` using `GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hc hB hG1 C RC hRC`. Establish `h70` using `GlobalTheory.T.lattice_image_base_change D R p w χ hc hB hG1 haf C RC hRC`.

Use `⟨⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩, fun τ => ⟨GlobalTheory.T.character_lattice_base_change_free D R p w χ hc hB hG1 hG2 haf C RC hRC τ, fun i => ⟨hdB C RC hRC τ i, hsB C RC hRC τ i⟩⟩⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[(hbc.2 τ).1, ← span_bcMap_annSub Ω C n i]`. Conclude with `(GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C (Fin n)) (D.af R p (χ τ)) (annSub Ω n i) (h68.1 τ).1.1 (hG2.ann τ i)).1`. Rewrite using `[(h69 τ).1 i]`.

Conclude with `loc_free_base_change R RC hRC (hG2.kk τ i)`. Use `beta_reduce`. Rewrite using `[(h69 τ).2 i, show AddMonoidHom.snd C (Fin (r τ) → C) = (LinearMap.snd C C (Fin (r τ) → C)).toAddMonoidHom from rfl, SpanExact.map_spanOver]`. Establish `himg : (LinearMap.snd C C (Fin (r τ) → C)) '' (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin (r τ))) '' (D.stepGraph τ (χ τ) i : Set _)) = bcMap Ω C (Fin (r τ)) '' ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd Ω (Fin (r τ) → Ω)) : Set _)`. Rewrite using `[AddSubgroup.coe_map, Set.image_image, Set.image_image]`.

Both sides reduce to the same expression. Rewrite using `[himg]`. Conclude with `loc_free_base_change R RC hRC (hG2.step τ i)`. Use `beta_reduce`. Rewrite using `[h70 τ]`.

Conclude with `loc_free_base_change R RC hRC (hG2.im τ)`.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → (∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) ∧ ∀ i, LocFree R 1 (D.dId R p (χ τ) i) ∧ LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₂ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) ∧ ∀ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) ∧ ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG1 hG2 haf
  obtain ⟨hdL, hdB⟩ := GlobalTheory.T.character_lattice_fibre_ideal_locally_free D R p w χ hc hB hG1 hG2
  obtain ⟨hsL, hsB⟩ := GlobalTheory.T.character_lattice_graph_comap_locally_free D R p w χ hc hB hG1 hG2
  have hkL := GlobalTheory.T.character_lattice_kernel_locally_free D R p w χ hc hB hG1 hG2 haf
  have h68 := GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG1
  refine ⟨fun τ => ⟨hkL τ, fun i => ⟨hdL τ i, hsL τ i⟩⟩, ?_⟩
  intro C _ _ _ _ RC hRC
  have hbc := h68.2 C RC hRC
  have h69 := GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hc hB hG1 C RC hRC
  have h70 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hB hG1 haf C RC hRC
  refine ⟨⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩,
    fun τ => ⟨GlobalTheory.T.character_lattice_base_change_free D R p w χ hc hB hG1 hG2 haf C RC hRC τ,
      fun i => ⟨hdB C RC hRC τ i, hsB C RC hRC τ i⟩⟩⟩
  · beta_reduce
    rw [(hbc.2 τ).1, ← span_bcMap_annSub Ω C n i]
    exact (GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C (Fin n))
      (D.af R p (χ τ)) (annSub Ω n i) (h68.1 τ).1.1 (hG2.ann τ i)).1
  · rw [(h69 τ).1 i]
    exact loc_free_base_change R RC hRC (hG2.kk τ i)
  · beta_reduce
    rw [(h69 τ).2 i,
      show AddMonoidHom.snd C (Fin (r τ) → C) = (LinearMap.snd C C (Fin (r τ) → C)).toAddMonoidHom
        from rfl, SpanExact.map_spanOver]
    have himg : (LinearMap.snd C C (Fin (r τ) → C)) ''
        (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin (r τ))) '' (D.stepGraph τ (χ τ) i : Set _)) =
          bcMap Ω C (Fin (r τ)) ''
            ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd Ω (Fin (r τ) → Ω)) : Set _) := by
      rw [AddSubgroup.coe_map, Set.image_image, Set.image_image]
      rfl
    rw [himg]
    exact loc_free_base_change R RC hRC (hG2.step τ i)
  · beta_reduce
    rw [h70 τ]
    exact loc_free_base_change R RC hRC (hG2.im τ)

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
