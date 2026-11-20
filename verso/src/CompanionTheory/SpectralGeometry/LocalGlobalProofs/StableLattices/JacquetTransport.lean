import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviSubspaceInvariantUnderBlocksStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantBlockEigenvalueStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigenStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

variable {n : ℕ}

/- English proof (translation)
Unfold `plab`. Rewrite using `[Finset.prod_subtype (Finset.univ.filter fun s => L s = k) (p := fun t => L t = k) (by simp)]`. Conclude with `(Equiv.prod_comp e (fun t : {t // L t = k} => Z + ψ t)).symm`.
-/
theorem plab_equiv (ψ : Fin n → ℂ) (L : Fin n → Fin 3) (k : Fin 3) {m : ℕ} (e : Fin m ≃ {t // L t = k}) (Z : ℂ) :
    plab ψ L k Z = ∏ a, (Z + ψ (e a)) := by
  classical
  unfold plab
  rw [Finset.prod_subtype (Finset.univ.filter fun s => L s = k) (p := fun t => L t = k) (by simp)]
  exact (Equiv.prod_comp e (fun t : {t // L t = k} => Z + ψ t)).symm

/- English proof (translation)
Unfold `plab Formalism.QuantumDeterminants.capP`. Conclude with `Finset.prod_fiberwise Finset.univ L (fun s => Y + ψ s)`.
-/
theorem prod_plab (ψ : Fin n → ℂ) (L : Fin n → Fin 3) (Y : ℂ) : ∏ i, plab ψ L i Y = Formalism.QuantumDeterminants.capP ψ Y := by
  classical
  unfold plab Formalism.QuantumDeterminants.capP
  exact Finset.prod_fiberwise Finset.univ L (fun s => Y + ψ s)

/- English proof (translation)
Unfold `plab`. Use `Finset.prod_equiv (Equiv.swap r s) (by simp) fun t _ => ?_` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `h1 : t = r`. Substitute `h1` using the available equality.

Distinguish the cases in `h2 : t = s`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, h2, Pi.single_apply]`. Distinguish the cases in `h2 : t = s`.

Substitute `h2` using the available equality. Simplify using `[h, h1, Pi.single_apply]`. Simplify using `[Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2, Pi.single_apply]`.
-/
theorem plab_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) (r s : Fin n) (h : χ r = χ s) (i : Fin 3) (Y : ℂ) :
    plab (χ + Pi.single s 1) (L ∘ Equiv.swap r s) i Y = plab (χ + Pi.single r 1) L i Y := by
  classical
  unfold plab
  refine Finset.prod_equiv (Equiv.swap r s) (by simp) fun t _ => ?_
  congr 1
  by_cases h1 : t = r
  · subst h1
    by_cases h2 : t = s
    · subst h2; simp
    · simp [h, h2, Pi.single_apply]
  · by_cases h2 : t = s
    · subst h2
      simp [h, h1, Pi.single_apply]
    · simp [Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2, Pi.single_apply]

/- English proof (translation)
Introduce `i`. Rewrite using `[← h i]`. Use `Finset.card_equiv (Equiv.swap r s) fun t => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem isLabel_swap {j : ℕ} {L : Fin n → Fin 3} (h : IsLabel j L) (r s : Fin n) : IsLabel j (L ∘ Equiv.swap r s) := by
  classical
  intro i
  rw [← h i]
  refine Finset.card_equiv (Equiv.swap r s) fun t => ?_
  simp

/- English proof (translation)
Distinguish the cases in `hrs : r = s`. Rewrite using `[hrs]`. Take `⟨Y, hY⟩` from `Infinite.exists_notMem_finset (Finset.univ.image fun t => -χ t)`. Establish `hne : ∀ t, Y + χ t ≠ 0` using `fun t h0 => hY (Finset.mem_image.2 ⟨t, Finset.mem_univ _, by linear_combination -h0⟩)`. Establish `split : ∀ f : Fin n → ℂ, ∏ t, f t = f r * (f s * ∏ t ∈ (Finset.univ.erase r).erase s, f t)`.

Introduce `f`. Rewrite using `[Finset.mul_prod_erase _ f (Finset.mem_erase.2 ⟨Ne.symm hrs, Finset.mem_univ _⟩), Finset.mul_prod_erase _ f (Finset.mem_univ _)]`. Establish `hY'` using `(split (fun t : Fin n => Y + (χ + Pi.single r 1 : Fin n → ℂ) t)).symm.trans ((h Y).trans (split (fun t : Fin n => Y + (χ + Pi.single s 1 : Fin n → ℂ) t)))`. Use `beta_reduce at hY'`. Establish `hc : ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single r 1 : Fin n → ℂ) t) = ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t)`.

Use `Finset.prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `h1 : t ≠ s` using `(Finset.mem_erase.1 ht).1`. Establish `h2 : t ≠ r` using `(Finset.mem_erase.1 (Finset.mem_erase.1 ht).2).1`. Simplify using `[Pi.single_apply, h1, h2]`. Rewrite `hY'` using `[hc]`.

Establish `hP : ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun t ht => ?_` and prove the remaining obligations. Establish `h1 : t ≠ s` using `(Finset.mem_erase.1 ht).1`. Simplify `hne t` using `[Pi.single_apply, h1]`. Generalize the expression as in `(∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t)) = Pr at hY' hP`.

Establish `e1 : (χ + Pi.single r 1 : Fin n → ℂ) r = χ r + 1` using `by simp`. Establish `e2 : (χ + Pi.single r 1 : Fin n → ℂ) s = χ s` using `by simp [Pi.single_apply, Ne.symm hrs]`. Establish `e3 : (χ + Pi.single s 1 : Fin n → ℂ) r = χ r` using `by simp [Pi.single_apply, hrs]`. Establish `e4 : (χ + Pi.single s 1 : Fin n → ℂ) s = χ s + 1` using `by simp`. Rewrite `hY'` using `[e1, e2, e3, e4]`.

Establish `h0 : Pr * (χ r - χ s) = 0` using `by linear_combination -hY'`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP)`.
-/
theorem entry_eq_of_capP (χ : Fin n → ℂ) (r s : Fin n)
    (h : ∀ Y, Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y = Formalism.QuantumDeterminants.capP (χ + Pi.single s 1) Y) : χ r = χ s := by
  by_cases hrs : r = s
  · rw [hrs]
  obtain ⟨Y, hY⟩ := Infinite.exists_notMem_finset (Finset.univ.image fun t => -χ t)
  have hne : ∀ t, Y + χ t ≠ 0 := fun t h0 => hY (Finset.mem_image.2 ⟨t, Finset.mem_univ _, by linear_combination -h0⟩)
  have split : ∀ f : Fin n → ℂ, ∏ t, f t = f r * (f s * ∏ t ∈ (Finset.univ.erase r).erase s, f t) := by
    intro f
    rw [Finset.mul_prod_erase _ f (Finset.mem_erase.2 ⟨Ne.symm hrs, Finset.mem_univ _⟩),
      Finset.mul_prod_erase _ f (Finset.mem_univ _)]
  have hY' := (split (fun t : Fin n => Y + (χ + Pi.single r 1 : Fin n → ℂ) t)).symm.trans
    ((h Y).trans (split (fun t : Fin n => Y + (χ + Pi.single s 1 : Fin n → ℂ) t)))
  beta_reduce at hY'
  have hc : ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single r 1 : Fin n → ℂ) t) =
      ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    have h1 : t ≠ s := (Finset.mem_erase.1 ht).1
    have h2 : t ≠ r := (Finset.mem_erase.1 (Finset.mem_erase.1 ht).2).1
    simp [Pi.single_apply, h1, h2]
  rw [hc] at hY'
  have hP : ∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    have h1 : t ≠ s := (Finset.mem_erase.1 ht).1
    simpa [Pi.single_apply, h1] using hne t
  generalize (∏ t ∈ (Finset.univ.erase r).erase s, (Y + (χ + Pi.single s 1 : Fin n → ℂ) t)) = Pr at hY' hP
  have e1 : (χ + Pi.single r 1 : Fin n → ℂ) r = χ r + 1 := by simp
  have e2 : (χ + Pi.single r 1 : Fin n → ℂ) s = χ s := by simp [Pi.single_apply, Ne.symm hrs]
  have e3 : (χ + Pi.single s 1 : Fin n → ℂ) r = χ r := by simp [Pi.single_apply, hrs]
  have e4 : (χ + Pi.single s 1 : Fin n → ℂ) s = χ s + 1 := by simp
  rw [e1, e2, e3, e4] at hY'
  have h0 : Pr * (χ r - χ s) = 0 := by linear_combination -hY'
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hP)

/- English proof (translation)
Introduce `a b c d`. Simplify `hE (ι a) (ι b) (ι c) (ι d)` using `[hι.eq_iff]`.
-/
theorem glRel_inj {A : Type*} [Ring A] {m : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) {ι : Fin m → Fin n}
    (hι : Function.Injective ι) : GlRel (fun a b => E (ι a) (ι b)) := by
  intro a b c d
  simpa [hι.eq_iff] using hE (ι a) (ι b) (ι c) (ι d)

def restrMod (P : GMod n) {m : ℕ} (ι : Fin m → Fin n) (hι : Function.Injective ι) (S : Submodule ℂ P.V)
    (hS : ∀ a b, ∀ x ∈ S, P.E (ι a) (ι b) x ∈ S) : GMod m where
  V := S
  E := fun a b => (P.E (ι a) (ι b)).restrict (hS a b)
  gl := fun a b c d => LinearMap.ext fun x => Subtype.ext (by
    have h := comm_apply P (ι a) (ι b) (ι c) (ι d) x
    simp only [hι.eq_iff] at h
    split_ifs at h ⊢ <;> simp [h] <;> abel)

/- English proof (translation)
Set `S : Finset (Fin 3)` to `univ.filter fun k => ∃ p, blk (stdBlocks d h) p = k ∧ ∃ x ∈ leviSub P d h χ L, θ p x ≠ 0`. Establish `hSne : S.Nonempty` using `⟨blk (stdBlocks d h) p0, mem_filter.2 ⟨mem_univ _, p0, rfl, v, hv, hne⟩⟩`. Take `⟨k, hk, hmaxk⟩ : ∃ k ∈ S, ∀ k' ∈ S, k' ≤ k` from `⟨S.max' hSne, S.max'_mem hSne, fun k' hk' => S.le_max' k' hk'⟩`. Establish `hmax : ∀ p, k < blk (stdBlocks d h) p → ∀ x ∈ leviSub P d h χ L, θ p x = 0`. Introduce `p hp x hx`.

Assume the negation of the conclusion as `hc`. Conclude with `absurd (hmaxk _ (mem_filter.2 ⟨mem_univ _, p, rfl, x, hx, hc⟩)) (not_le.2 hp)`. Take `⟨p1, hp1, x1, hx1, hne1⟩` from `(mem_filter.1 hk).2`. Choose the witnesses or unpack the hypotheses as in `⟨p', hp'⟩ : ∃ p' : Fin (d k), stdBlocks d h ⟨k, p'⟩ = p1 := by`. Take `⟨⟨k', p'⟩, rfl⟩` from `(stdBlocks d h).surjective p1`.

Establish `: k' = k` using `by simpa [blk] using hp1`. Substitute `this` using the available equality. Conclude with `⟨p', rfl⟩`. Set `ι : Fin (d k) → Fin n` to `fun a => stdBlocks d h ⟨k, a⟩`. Establish `hblk : ∀ a, blk (stdBlocks d h) (ι a) = k` using `fun a => by simp [blk, ι]`.

Establish `hι : Function.Injective ι` using `fun a b hab => by`. Use `(stdBlocks d h).injective hab` as an intermediate fact. Simplify using `using this`. Set `M : GMod (d k)` to `restrMod P ι hι (leviSub P d h χ L) (fun a b x hx => GlobalTheory.T.levi_subspace_invariant_under_blocks P d h χ L _ _ (by rw [hblk, hblk]) x hx)`. Establish `hc : Fintype.card {t // L t = k} = d k` using `by rw [Fintype.card_subtype]; exact hL k`.

Set `e' : Fin (d k) ≃ {t // L t = k}` to `(Fintype.equivFinOfCardEq hc).symm`. Set `c : ℂ` to `(modExp (fun i => Fin (d i)) k : ℂ) / 2`. Set `χ' : Fin (d k) → ℂ` to `fun a => χ (e' a) + c`. Establish `hchar : HasChar M χ'`. Use `⟨1, fun Y => ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_one]`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Establish `h1` using `qdet_lin (leviSub P d h χ L).subtype M.E (bops P d h k) (fun a b x => rfl) (Y + ((d k : ℂ) - 1) / 2) x`. Establish `h2` using `x.2.2 k (Y + c)`. Establish `h3 : Qd P d h k (Y + c) = qdet (bops P d h k) (Y + ((d k : ℂ) - 1) / 2)`.

Unfold `Qd`. Use `congr 1`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : plab χ L k (Y + c) = Formalism.QuantumDeterminants.capP χ' Y`.

Rewrite using `[plab_equiv χ L k e']`. Unfold `Formalism.QuantumDeterminants.capP`. Conclude with `Finset.prod_congr rfl fun a _ => by simp only [χ']; ring`. Rewrite `h2` using `[h3, h4]`. Establish `h5 : (leviSub P d h χ L).subtype ((qdet M.E (Y + ((d k : ℂ) - 1) / 2)) x) = Formalism.QuantumDeterminants.capP χ' Y • (leviSub P d h χ L).subtype x` using `h1.trans h2`.

Conclude with `sub_eq_zero.2 h5`. Set `incl : M.V →ₗ[ℂ] P.V` to `(leviSub P d h χ L).subtype`. Establish `hincl : ∀ x : M.V, incl x ∈ leviSub P d h χ L` using `fun x => x.2`. Establish `hinclE : ∀ a b (x : M.V), incl (M.E a b x) = P.E (ι a) (ι b) (incl x)` using `fun a b x => rfl`. Set `Φ : (Fin (d k) → M.V) →ₗ[ℂ] Q.V` to `∑ a, (θ (ι a)) ∘ₗ incl ∘ₗ (LinearMap.proj a)`.

Establish `hΦa : ∀ u, Φ u = ∑ a, θ (ι a) (incl (u a))` using `fun u => by simp [Φ, LinearMap.sum_apply]`. Establish `hΦ : ∀ a b u, Φ (tensE M a b u) = bops Q d h k a b (Φ u)`. Introduce `a b u`. Rewrite using `[hΦa, hΦa, map_sum]`. Establish `e1 : ∀ p, θ (ι p) (incl (tensE M a b u p)) = θ (ι p) (P.E (ι a) (ι b) (incl (u p))) + if p = a then θ (ι a) (incl (u b)) else 0`.

Introduce `p`. Rewrite using `[tensE_apply, map_add, map_add, hinclE]`. Distinguish the cases in `hp : p = a`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hp]`. Establish `e2 : ∀ p, bops Q d h k a b (θ (ι p) (incl (u p))) = θ (ι p) (P.E (ι a) (ι b) (incl (u p))) + if p = b then θ (ι a) (incl (u p)) else 0`. Introduce `p`. Simplify using `only [bops]`. Rewrite using `[hθ]`.

Simplify using `only [show stdBlocks d h ⟨k, a⟩ = ι a from rfl, show stdBlocks d h ⟨k, b⟩ = ι b from rfl, hι.eq_iff]`. Simplify using `only [e1, e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hΦne : Φ ≠ 0`. Introduce `h0`. Set `x1' : M.V` to `⟨x1, hx1⟩`.

Establish `e` using `LinearMap.congr_fun h0 (Pi.single p' x1')`. Rewrite `e` using `[hΦa, Finset.sum_eq_single p']`. Rewrite `e` using `[Pi.single_eq_same]`. Apply `hne1` to reduce the goal to its premises. Rewrite using `[← hp']`.

Conclude with `e`. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb, map_zero, map_zero]`. Simplify using the standard rewrite rules. Take `⟨r, _, ⟨u, rfl⟩, hw0, hwq⟩` from `GlobalTheory.T.tensor_quotient_quantum_determinant_eigen hS hT M χ' hchar (bops Q d h k) (glRel_inj Q.gl hι) Φ hΦ hΦne`.

Use `⟨Φ u, hw0, ?_, (e' r).1, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Rewrite using `[hΦa, map_sum]`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Rewrite using `[hθ, (hincl (u p)).1 a b hab, map_zero, zero_add]`.

Use `split_ifs with hp`. Conclude with `hmax a (by rw [← hp, hblk] at hab; exact hab) _ (hincl (u p))`. Both sides reduce to the same expression. Introduce `i Y`. Break down `eq_or_ne i k with hi | hik` into its components or cases.

Rewrite using `[hi]`. Establish `h5` using `hwq (Y - c)`. Establish `h6 : Qd Q d h k Y = qdet (bops Q d h k) (Y - c + ((d k : ℂ) - 1) / 2)`. Unfold `Qd`. Use `congr 1`.

Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree. Establish `h7 : Formalism.QuantumDeterminants.capP (χ' + Pi.single r 1) (Y - c) = plab (χ + Pi.single (e' r).1 1) L k Y`. Rewrite using `[plab_equiv _ L k e']`. Unfold `Formalism.QuantumDeterminants.capP`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `har : a = r`. Substitute `har` using the available equality. Simplify using `[χ']`. Apply the tactic sequence `try ring`.

Establish `: (e' a).1 ≠ (e' r).1` using `fun h0 => har (e'.injective (Subtype.ext h0))`. Simplify using `[χ', Pi.single_apply, har, this]`. Apply the tactic sequence `try ring`. Rewrite using `[h6, h5, h7]`. Establish `h8 : plab (χ + Pi.single (e' r).1 1) L i Y = plab χ L i Y`.

Unfold `plab`. Use `Finset.prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `hti : L t = i` using `(Finset.mem_filter.1 ht).2`. Establish `: t ≠ (e' r).1` using `fun h0 => hik (by rw [← hti, h0]; exact (e' r).2)`. Simplify using `[Pi.single_apply, this]`.

Rewrite using `[h8, hΦa, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `h9` using `qdet_lin (θ (ι p)) (bops P d h i) (bops Q d h i) (fun a b y => by`. Simplify using `only [bops]`. Rewrite using `[hθ, if_neg, add_zero]`.

Introduce `h0`. Establish `h1` using `hblk p`. Rewrite `h1` using `[h0]`. Simplify using `[blk] at h1`. Conclude with `hik h1) (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2) (incl (u p))`.

Establish `h10` using `(hincl (u p)).2 i Y`. Unfold `Qd at h10 ⊢`. Rewrite using `[← h9, h10, map_smul]`.
-/
theorem block_raise (hS : StepChar) (hT : TensDecomp) (P Q : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n)
    (θ : Fin n → P.V →ₗ[ℂ] Q.V)
    (hθ : ∀ a b p x, Q.E a b (θ p x) = θ p (P.E a b x) + if p = b then θ a x else 0)
    (χ : Fin n → ℂ) (L : Fin n → Fin 3) (hL : ∀ i, (univ.filter fun s => L s = i).card = d i)
    (v : P.V) (hv : v ∈ leviSub P d h χ L) (p0 : Fin n) (hne : θ p0 v ≠ 0) :
    ∃ w : Q.V, w ≠ 0 ∧ (∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → Q.E a b w = 0) ∧
      ∃ r, ∀ i Y, Qd Q d h i Y w = plab (χ + Pi.single r 1) L i Y • w := by
  classical

  let S : Finset (Fin 3) := univ.filter fun k => ∃ p, blk (stdBlocks d h) p = k ∧ ∃ x ∈ leviSub P d h χ L, θ p x ≠ 0
  have hSne : S.Nonempty := ⟨blk (stdBlocks d h) p0, mem_filter.2 ⟨mem_univ _, p0, rfl, v, hv, hne⟩⟩
  obtain ⟨k, hk, hmaxk⟩ : ∃ k ∈ S, ∀ k' ∈ S, k' ≤ k := ⟨S.max' hSne, S.max'_mem hSne, fun k' hk' => S.le_max' k' hk'⟩
  have hmax : ∀ p, k < blk (stdBlocks d h) p → ∀ x ∈ leviSub P d h χ L, θ p x = 0 := by
    intro p hp x hx
    by_contra hc
    exact absurd (hmaxk _ (mem_filter.2 ⟨mem_univ _, p, rfl, x, hx, hc⟩)) (not_le.2 hp)
  obtain ⟨p1, hp1, x1, hx1, hne1⟩ := (mem_filter.1 hk).2
  obtain ⟨p', hp'⟩ : ∃ p' : Fin (d k), stdBlocks d h ⟨k, p'⟩ = p1 := by
    obtain ⟨⟨k', p'⟩, rfl⟩ := (stdBlocks d h).surjective p1
    have : k' = k := by simpa [blk] using hp1
    subst this
    exact ⟨p', rfl⟩

  let ι : Fin (d k) → Fin n := fun a => stdBlocks d h ⟨k, a⟩
  have hblk : ∀ a, blk (stdBlocks d h) (ι a) = k := fun a => by simp [blk, ι]
  have hι : Function.Injective ι := fun a b hab => by
    have := (stdBlocks d h).injective hab
    simpa using this
  let M : GMod (d k) := restrMod P ι hι (leviSub P d h χ L)
    (fun a b x hx => GlobalTheory.T.levi_subspace_invariant_under_blocks P d h χ L _ _ (by rw [hblk, hblk]) x hx)
  have hc : Fintype.card {t // L t = k} = d k := by rw [Fintype.card_subtype]; exact hL k
  let e' : Fin (d k) ≃ {t // L t = k} := (Fintype.equivFinOfCardEq hc).symm
  let c : ℂ := (modExp (fun i => Fin (d i)) k : ℂ) / 2
  let χ' : Fin (d k) → ℂ := fun a => χ (e' a) + c
  have hchar : HasChar M χ' := by
    refine ⟨1, fun Y => ?_⟩
    rw [pow_one]
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h1 := qdet_lin (leviSub P d h χ L).subtype M.E (bops P d h k) (fun a b x => rfl) (Y + ((d k : ℂ) - 1) / 2) x
    have h2 := x.2.2 k (Y + c)
    have h3 : Qd P d h k (Y + c) = qdet (bops P d h k) (Y + ((d k : ℂ) - 1) / 2) := by
      unfold Qd
      congr 1
      simp only [c]
      ring
    have h4 : plab χ L k (Y + c) = Formalism.QuantumDeterminants.capP χ' Y := by
      rw [plab_equiv χ L k e']
      unfold Formalism.QuantumDeterminants.capP
      exact Finset.prod_congr rfl fun a _ => by simp only [χ']; ring
    rw [h3, h4] at h2
    have h5 : (leviSub P d h χ L).subtype ((qdet M.E (Y + ((d k : ℂ) - 1) / 2)) x) =
        Formalism.QuantumDeterminants.capP χ' Y • (leviSub P d h χ L).subtype x := h1.trans h2
    exact sub_eq_zero.2 h5

  let incl : M.V →ₗ[ℂ] P.V := (leviSub P d h χ L).subtype
  have hincl : ∀ x : M.V, incl x ∈ leviSub P d h χ L := fun x => x.2
  have hinclE : ∀ a b (x : M.V), incl (M.E a b x) = P.E (ι a) (ι b) (incl x) := fun a b x => rfl
  let Φ : (Fin (d k) → M.V) →ₗ[ℂ] Q.V := ∑ a, (θ (ι a)) ∘ₗ incl ∘ₗ (LinearMap.proj a)
  have hΦa : ∀ u, Φ u = ∑ a, θ (ι a) (incl (u a)) := fun u => by simp [Φ, LinearMap.sum_apply]
  have hΦ : ∀ a b u, Φ (tensE M a b u) = bops Q d h k a b (Φ u) := by
    intro a b u
    rw [hΦa, hΦa, map_sum]
    have e1 : ∀ p, θ (ι p) (incl (tensE M a b u p)) =
        θ (ι p) (P.E (ι a) (ι b) (incl (u p))) + if p = a then θ (ι a) (incl (u b)) else 0 := by
      intro p
      rw [tensE_apply, map_add, map_add, hinclE]
      by_cases hp : p = a
      · subst hp; simp
      · simp [hp]
    have e2 : ∀ p, bops Q d h k a b (θ (ι p) (incl (u p))) =
        θ (ι p) (P.E (ι a) (ι b) (incl (u p))) + if p = b then θ (ι a) (incl (u p)) else 0 := by
      intro p
      simp only [bops]
      rw [hθ]
      simp only [show stdBlocks d h ⟨k, a⟩ = ι a from rfl, show stdBlocks d h ⟨k, b⟩ = ι b from rfl, hι.eq_iff]
    simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hΦne : Φ ≠ 0 := by
    intro h0
    let x1' : M.V := ⟨x1, hx1⟩
    have e := LinearMap.congr_fun h0 (Pi.single p' x1')
    rw [hΦa, Finset.sum_eq_single p'] at e
    · rw [Pi.single_eq_same] at e
      apply hne1
      rw [← hp']
      exact e
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero, map_zero]
    · simp
  obtain ⟨r, _, ⟨u, rfl⟩, hw0, hwq⟩ := GlobalTheory.T.tensor_quotient_quantum_determinant_eigen hS hT M χ' hchar (bops Q d h k) (glRel_inj Q.gl hι) Φ hΦ hΦne
  refine ⟨Φ u, hw0, ?_, (e' r).1, ?_⟩
  · intro a b hab
    rw [hΦa, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hθ, (hincl (u p)).1 a b hab, map_zero, zero_add]
    split_ifs with hp
    · exact hmax a (by rw [← hp, hblk] at hab; exact hab) _ (hincl (u p))
    · rfl
  · intro i Y
    rcases eq_or_ne i k with hi | hik
    · rw [hi]
      have h5 := hwq (Y - c)
      have h6 : Qd Q d h k Y = qdet (bops Q d h k) (Y - c + ((d k : ℂ) - 1) / 2) := by
        unfold Qd
        congr 1
        simp only [c]
        ring
      have h7 : Formalism.QuantumDeterminants.capP (χ' + Pi.single r 1) (Y - c) = plab (χ + Pi.single (e' r).1 1) L k Y := by
        rw [plab_equiv _ L k e']
        unfold Formalism.QuantumDeterminants.capP
        refine Finset.prod_congr rfl fun a _ => ?_
        by_cases har : a = r
        · subst har
          simp [χ']
          try ring
        · have : (e' a).1 ≠ (e' r).1 := fun h0 => har (e'.injective (Subtype.ext h0))
          simp [χ', Pi.single_apply, har, this]
          try ring
      rw [h6, h5, h7]
    · have h8 : plab (χ + Pi.single (e' r).1 1) L i Y = plab χ L i Y := by
        unfold plab
        refine Finset.prod_congr rfl fun t ht => ?_
        have hti : L t = i := (Finset.mem_filter.1 ht).2
        have : t ≠ (e' r).1 := fun h0 => hik (by rw [← hti, h0]; exact (e' r).2)
        simp [Pi.single_apply, this]
      rw [h8, hΦa, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have h9 := qdet_lin (θ (ι p)) (bops P d h i) (bops Q d h i) (fun a b y => by
        simp only [bops]
        rw [hθ, if_neg, add_zero]
        intro h0
        have h1 := hblk p
        rw [h0] at h1
        simp [blk] at h1
        exact hik h1) (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2) (incl (u p))
      have h10 := (hincl (u p)).2 i Y
      unfold Qd at h10 ⊢
      rw [← h9, h10, map_smul]

def dualL (V : Type) [AddCommGroup V] [Module ℂ V] : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (Module.Dual ℂ V) where
  toFun T := T.dualMap
  map_add' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => by simp [LinearMap.dualMap_apply]
  map_smul' _ _ := LinearMap.ext fun _ => LinearMap.ext fun _ => by simp [LinearMap.dualMap_apply]

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => LinearMap.ext fun _ => rfl`.
-/
theorem dualL_one (V : Type) [AddCommGroup V] [Module ℂ V] : dualL V 1 = 1 :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => LinearMap.ext fun _ => rfl`.
-/
theorem dualL_mul (V : Type) [AddCommGroup V] [Module ℂ V] (x y : Module.End ℂ V) :
    dualL V (x * y) = dualL V y * dualL V x :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [dualL_one]`. Consider the case `succ k ih => rw [pow_succ, dualL_mul, ih, pow_succ']`.
-/
theorem dualL_pow (V : Type) [AddCommGroup V] [Module ℂ V] (x : Module.End ℂ V) (k : ℕ) :
    dualL V (x ^ k) = dualL V x ^ k := by
  induction k with
  | zero => simp [dualL_one]
  | succ k ih => rw [pow_succ, dualL_mul, ih, pow_succ']

/- English proof (translation)
The claim follows from `GlobalTheory.T.quantum_determinant_anti_homomorphism (dualL Y.V) (dualL_one _) (dualL_mul _) (fun a b => Y.E (ι a) (ι b)) (glRel_inj Y.gl hι) u`.
-/
theorem qdet_tr (Y : GMod n) {m : ℕ} (ι : Fin m → Fin n) (hι : Function.Injective ι) (u : ℂ) :
    qdet (fun a b => (trMod Y).E (ι a) (ι b)) u = (qdet (fun a b => Y.E (ι a) (ι b)) u).dualMap :=
  GlobalTheory.T.quantum_determinant_anti_homomorphism (dualL Y.V) (dualL_one _) (dualL_mul _) (fun a b => Y.E (ι a) (ι b)) (glRel_inj Y.gl hι) u

/- English proof (translation)
The claim follows from `qdet_tr Y (fun p => stdBlocks d h ⟨i, p⟩) (fun a b hab => by have := (stdBlocks d h).injective hab simpa using this) _`.
-/
theorem Qd_tr (Y : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (i : Fin 3) (c : ℂ) :
    Qd (trMod Y) d h i c = (Qd Y d h i c).dualMap :=
  qdet_tr Y (fun p => stdBlocks d h ⟨i, p⟩) (fun a b hab => by
    have := (stdBlocks d h).injective hab
    simpa using this) _

/- English proof (translation)
Take `⟨k, hk⟩` from `hY`. Use `⟨k, fun c => ?_⟩` and prove the remaining obligations. Establish `e : qdet (trMod Y).E (c + ((n : ℂ) - 1) / 2) = dualL Y.V (qdet Y.E (c + ((n : ℂ) - 1) / 2))` using `qdet_tr Y id Function.injective_id _`. Establish `e3 : (dualL Y.V (qdet Y.E (c + ((n : ℂ) - 1) / 2)) - Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ (Module.Dual ℂ Y.V))) ^ k = 0`. Rewrite using `[← dualL_one, ← map_smul, ← map_sub, ← dualL_pow, hk c, map_zero]`.

Conclude with `(congrArg (fun T : Module.End ℂ (Module.Dual ℂ Y.V) => (T - Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ (Module.Dual ℂ Y.V))) ^ k) e).trans e3`.
-/
theorem hasChar_tr (Y : GMod n) {χ : Fin n → ℂ} (hY : HasChar Y χ) : HasChar (trMod Y) χ := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun c => ?_⟩
  have e : qdet (trMod Y).E (c + ((n : ℂ) - 1) / 2) = dualL Y.V (qdet Y.E (c + ((n : ℂ) - 1) / 2)) :=
    qdet_tr Y id Function.injective_id _
  have e3 : (dualL Y.V (qdet Y.E (c + ((n : ℂ) - 1) / 2)) -
      Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ (Module.Dual ℂ Y.V))) ^ k = 0 := by
    rw [← dualL_one, ← map_smul, ← map_sub, ← dualL_pow, hk c, map_zero]
  exact (congrArg (fun T : Module.End ℂ (Module.Dual ℂ Y.V) =>
    (T - Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ (Module.Dual ℂ Y.V))) ^ k) e).trans e3

def sqMod (Y : GMod n) (S1 S2 : Submodule ℂ (Module.Dual ℂ Y.V)) (h1 : ∀ a b, ∀ φ ∈ S1, (Y.E a b).dualMap φ ∈ S1)
    (h2 : ∀ a b, ∀ φ ∈ S2, (Y.E a b).dualMap φ ∈ S2) : GMod n :=
  quoMod ((trMod Y).sub S1 (fun a b φ hφ => h1 b a φ hφ)) (S2.comap S1.subtype) (fun a b _ hx => h2 b a _ hx)

section Sq

variable (Y : GMod n) (S1 S2 : Submodule ℂ (Module.Dual ℂ Y.V)) (h1 : ∀ a b, ∀ φ ∈ S1, (Y.E a b).dualMap φ ∈ S1)
  (h2 : ∀ a b, ∀ φ ∈ S2, (Y.E a b).dualMap φ ∈ S2)

def sqMk : S1 →ₗ[ℂ] (sqMod Y S1 S2 h1 h2).V := (S2.comap S1.subtype).mkQ

/- English proof (translation)
The claim follows from `Submodule.mkQ_surjective _`.
-/
theorem sqMk_surj : Function.Surjective (sqMk Y S1 S2 h1 h2) := Submodule.mkQ_surjective _

/- English proof (translation)
The claim follows from `Submodule.Quotient.mk_eq_zero _`.
-/
theorem sqMk_zero (x : S1) : sqMk Y S1 S2 h1 h2 x = 0 ↔ (x : Module.Dual ℂ Y.V) ∈ S2 :=
  Submodule.Quotient.mk_eq_zero _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sq_E (a b : Fin n) (x : S1) :
    (sqMod Y S1 S2 h1 h2).E a b (sqMk Y S1 S2 h1 h2 x) = sqMk Y S1 S2 h1 h2 ⟨(Y.E b a).dualMap x, h1 b a _ x.2⟩ := rfl

/- English proof (translation)
Set `Y1 : GMod n` to `(trMod Y).sub S1 (fun a b φ hφ => h1 b a φ hφ)`. Use `⟨Qd Y1 d h i c x, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `qdet_lin (V := S1) S1.subtype (bops Y1 d h i) (bops (trMod Y) d h i) (fun a b x => rfl) (c + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2) x`. Conclude with `e.trans (LinearMap.congr_fun (Qd_tr Y d h i c) (show (trMod Y).V from x.1))`. Conclude with `(qdet_lin (V := S1) (sqMk Y S1 S2 h1 h2) (bops Y1 d h i) (bops (sqMod Y S1 S2 h1 h2) d h i) (fun a b x => rfl) _ x).symm`.
-/
theorem sq_Qd (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (i : Fin 3) (c : ℂ) (x : S1) :
    ∃ y : S1, (y : Module.Dual ℂ Y.V) = (Qd Y d h i c).dualMap x ∧
      Qd (sqMod Y S1 S2 h1 h2) d h i c (sqMk Y S1 S2 h1 h2 x) = sqMk Y S1 S2 h1 h2 y := by
  let Y1 : GMod n := (trMod Y).sub S1 (fun a b φ hφ => h1 b a φ hφ)
  refine ⟨Qd Y1 d h i c x, ?_, ?_⟩
  · have e := qdet_lin (V := S1) S1.subtype (bops Y1 d h i) (bops (trMod Y) d h i) (fun a b x => rfl)
      (c + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2) x
    exact e.trans (LinearMap.congr_fun (Qd_tr Y d h i c) (show (trMod Y).V from x.1))
  · exact (qdet_lin (V := S1) (sqMk Y S1 S2 h1 h2) (bops Y1 d h i) (bops (sqMod Y S1 S2 h1 h2) d h i)
      (fun a b x => rfl) _ x).symm

end Sq

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Establish `: (T - D • (1 : Module.End ℂ V)) w = (C - D) • w` using `by simp [h, sub_smul]`.

Rewrite using `[this, map_smul, ih, smul_smul, pow_succ']`.
-/
theorem eigen_pow {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (w : V) (C D : ℂ) (h : T w = C • w) (k : ℕ) :
    ((T - D • (1 : Module.End ℂ V)) ^ k) w = (C - D) ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have : (T - D • (1 : Module.End ℂ V)) w = (C - D) • w := by simp [h, sub_smul]
    rw [this, map_smul, ih, smul_smul, pow_succ']

/- English proof (translation)
Set `mkP` to `sqMk Y S1 S2 hS1 hS2`. Set `mkQ'` to `sqMk Y' T1 T2 hT1 hT2`. Set `R : Fin n → S1 →ₗ[ℂ] T1` to `fun p => (θ p).restrict (hθ1 p)`. Establish `hR : ∀ p, S2.comap S1.subtype ≤ (T2.comap T1.subtype).comap (R p)` using `fun p x hx => hθ2 p _ hx`. Set `θq : Fin n → (sqMod Y S1 S2 hS1 hS2).V →ₗ[ℂ] (sqMod Y' T1 T2 hT1 hT2).V` to `fun p => Submodule.mapQ _ _ (R p) (hR p)`.

Establish `hθq0 : ∀ p (x : S1), θq p (mkP x) = mkQ' (R p x)` using `fun p x => rfl`. Establish `hθq : ∀ a b p x, (sqMod Y' T1 T2 hT1 hT2).E a b (θq p x) = θq p ((sqMod Y S1 S2 hS1 hS2).E a b x) + if p = b then θq a x else 0`. Introduce `a b p x`. Take `⟨x, rfl⟩` from `sqMk_surj Y S1 S2 hS1 hS2 x`. Express the relevant statement in the definitionally equal form `(sqMod Y' T1 T2 hT1 hT2).E a b (θq p (mkP x)) = θq p ((sqMod Y S1 S2 hS1 hS2).E a b (mkP x)) + if p = b then θq a (mkP x) else 0`.

Rewrite using `[hθq0, hθq0]`. Express the relevant statement in the definitionally equal form `(sqMod Y' T1 T2 hT1 hT2).E a b (sqMk Y' T1 T2 hT1 hT2 (R p x)) = _`. Rewrite using `[sq_E]`. Express the relevant statement in the definitionally equal form `_ = θq p (sqMk Y S1 S2 hS1 hS2 ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) + _`. Rewrite using `[show θq p (sqMk Y S1 S2 hS1 hS2 ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) = mkQ' (R p ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) from rfl]`.

Distinguish the cases in `hp : p = b`. Rewrite using `[if_pos hp, ← map_add]`. Use `congrArg _ (Subtype.ext ?_)` and prove the remaining obligations. Use `hθ a b p x` as an intermediate fact. Rewrite `this` using `[if_pos hp]`.

Conclude with `this`. Rewrite using `[if_neg hp, add_zero]`. Use `congrArg _ (Subtype.ext ?_)` and prove the remaining obligations. Use `hθ a b p x` as an intermediate fact. Rewrite `this` using `[if_neg hp, add_zero]`.

Conclude with `this`. Establish `hv : mkP ⟨φ, hφ⟩ ∈ leviSub (sqMod Y S1 S2 hS1 hS2) d h χ L`. Use `⟨fun a b hab => ?_, fun i c => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(sqMod Y S1 S2 hS1 hS2).E a b (sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩) = 0`. Rewrite using `[sq_E, sqMk_zero]`.

Conclude with `hk b a hab`. Take `⟨y, hy1, hy2⟩` from `sq_Qd Y S1 S2 hS1 hS2 d h i c ⟨φ, hφ⟩`. Express the relevant statement in the definitionally equal form `Qd _ d h i c (sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩) = plab χ L i c • sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩`. Rewrite using `[hy2, ← map_smul, ← sub_eq_zero, ← map_sub, sqMk_zero]`. Use `hq i c` as an intermediate fact.

Rewrite `this` using `[← hy1]`. Conclude with `this`. Establish `hne' : θq p0 (mkP ⟨φ, hφ⟩) ≠ 0`. Rewrite using `[hθq0]`. Introduce `h0`.

Conclude with `hne ((sqMk_zero Y' T1 T2 hT1 hT2 _).1 h0)`. Take `⟨w, hw0, hwk, r, hwq⟩` from `block_raise hS hT _ _ d h θq hθq χ L hL _ hv p0 hne'`. Take `⟨ψ, rfl⟩` from `sqMk_surj Y' T1 T2 hT1 hT2 w`. Use `⟨ψ.1, ψ.2, fun h0 => hw0 ((sqMk_zero Y' T1 T2 hT1 hT2 _).2 h0), fun p q hpq => ?_, r, fun i c => ?_, fun c => ?_⟩` and prove the remaining obligations. Use `hwk q p hpq` as an intermediate fact.

Rewrite `this` using `[sq_E, sqMk_zero]`. Conclude with `this`. Take `⟨y, hy1, hy2⟩` from `sq_Qd Y' T1 T2 hT1 hT2 d h i c ψ`. Use `hwq i c` as an intermediate fact. Rewrite `this` using `[hy2, ← map_smul, ← sub_eq_zero, ← map_sub, sqMk_zero]`.

Rewrite using `[← hy1]`. Conclude with `this`. Establish `hQ` using `GlobalTheory.T.quantum_determinant_block_eigenvalue (sqMod Y' T1 T2 hT1 hT2) d h _ hwk (fun i c => plab (χ + Pi.single r 1) L i c) hwq c`. Rewrite `hQ` using `[prod_plab]`. Establish `hc1` using `hasChar_sub (trMod Y') T1 (fun a b φ hφ => hT1 b a φ hφ) (hasChar_tr Y' hchar)`.

Establish `hc2 : HasChar (sqMod Y' T1 T2 hT1 hT2) χ''` using `hasChar_quo _ _ _ hc1`. Take `⟨k, hkk⟩` from `hc2`. Establish `e` using `eigen_pow _ _ _ (Formalism.QuantumDeterminants.capP χ'' c) hQ k`. Rewrite `e` using `[hkk c]`. Assume the negation of the conclusion as `hne2`.

Establish `e'` using `e.symm`. Conclude with `hw0 ((smul_eq_zero.1 e').resolve_left (pow_ne_zero k (sub_ne_zero.2 hne2)))`.
-/
theorem sub_raise (hS : StepChar) (hT : TensDecomp) (Y Y' : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n)
    (S1 S2 : Submodule ℂ (Module.Dual ℂ Y.V)) (T1 T2 : Submodule ℂ (Module.Dual ℂ Y'.V))
    (hS1 : ∀ a b, ∀ φ ∈ S1, (Y.E a b).dualMap φ ∈ S1) (hS2 : ∀ a b, ∀ φ ∈ S2, (Y.E a b).dualMap φ ∈ S2)
    (hT1 : ∀ a b, ∀ φ ∈ T1, (Y'.E a b).dualMap φ ∈ T1) (hT2 : ∀ a b, ∀ φ ∈ T2, (Y'.E a b).dualMap φ ∈ T2)
    (θ : Fin n → Module.Dual ℂ Y.V →ₗ[ℂ] Module.Dual ℂ Y'.V)
    (hθ : ∀ a b p φ, (Y'.E b a).dualMap (θ p φ) = θ p ((Y.E b a).dualMap φ) + if p = b then θ a φ else 0)
    (hθ1 : ∀ p, ∀ φ ∈ S1, θ p φ ∈ T1) (hθ2 : ∀ p, ∀ φ ∈ S2, θ p φ ∈ T2)
    (χ : Fin n → ℂ) (L : Fin n → Fin 3) (hL : ∀ i, (univ.filter fun s => L s = i).card = d i)
    (φ : Module.Dual ℂ Y.V) (hφ : φ ∈ S1)
    (hk : ∀ p q, blk (stdBlocks d h) p < blk (stdBlocks d h) q → (Y.E p q).dualMap φ ∈ S2)
    (hq : ∀ i c, (Qd Y d h i c).dualMap φ - plab χ L i c • φ ∈ S2) (p0 : Fin n) (hne : θ p0 φ ∉ T2)
    (χ'' : Fin n → ℂ) (hchar : HasChar Y' χ'') :
    ∃ ψ ∈ T1, ψ ∉ T2 ∧ (∀ p q, blk (stdBlocks d h) p < blk (stdBlocks d h) q → (Y'.E p q).dualMap ψ ∈ T2) ∧
      ∃ r, (∀ i c, (Qd Y' d h i c).dualMap ψ - plab (χ + Pi.single r 1) L i c • ψ ∈ T2) ∧
        ∀ c, Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) c = Formalism.QuantumDeterminants.capP χ'' c := by
  let mkP := sqMk Y S1 S2 hS1 hS2
  let mkQ' := sqMk Y' T1 T2 hT1 hT2
  let R : Fin n → S1 →ₗ[ℂ] T1 := fun p => (θ p).restrict (hθ1 p)
  have hR : ∀ p, S2.comap S1.subtype ≤ (T2.comap T1.subtype).comap (R p) := fun p x hx => hθ2 p _ hx
  let θq : Fin n → (sqMod Y S1 S2 hS1 hS2).V →ₗ[ℂ] (sqMod Y' T1 T2 hT1 hT2).V :=
    fun p => Submodule.mapQ _ _ (R p) (hR p)
  have hθq0 : ∀ p (x : S1), θq p (mkP x) = mkQ' (R p x) := fun p x => rfl
  have hθq : ∀ a b p x, (sqMod Y' T1 T2 hT1 hT2).E a b (θq p x) =
      θq p ((sqMod Y S1 S2 hS1 hS2).E a b x) + if p = b then θq a x else 0 := by
    intro a b p x
    obtain ⟨x, rfl⟩ := sqMk_surj Y S1 S2 hS1 hS2 x
    change (sqMod Y' T1 T2 hT1 hT2).E a b (θq p (mkP x)) = θq p ((sqMod Y S1 S2 hS1 hS2).E a b (mkP x)) + if p = b then θq a (mkP x) else 0
    rw [hθq0, hθq0]
    change (sqMod Y' T1 T2 hT1 hT2).E a b (sqMk Y' T1 T2 hT1 hT2 (R p x)) = _
    rw [sq_E]
    change _ = θq p (sqMk Y S1 S2 hS1 hS2 ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) + _
    rw [show θq p (sqMk Y S1 S2 hS1 hS2 ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) = mkQ' (R p ⟨(Y.E b a).dualMap x, hS1 b a _ x.2⟩) from rfl]
    by_cases hp : p = b
    · rw [if_pos hp, ← map_add]
      refine congrArg _ (Subtype.ext ?_)
      have := hθ a b p x
      rw [if_pos hp] at this
      exact this
    · rw [if_neg hp, add_zero]
      refine congrArg _ (Subtype.ext ?_)
      have := hθ a b p x
      rw [if_neg hp, add_zero] at this
      exact this
  have hv : mkP ⟨φ, hφ⟩ ∈ leviSub (sqMod Y S1 S2 hS1 hS2) d h χ L := by
    refine ⟨fun a b hab => ?_, fun i c => ?_⟩
    · change (sqMod Y S1 S2 hS1 hS2).E a b (sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩) = 0
      rw [sq_E, sqMk_zero]
      exact hk b a hab
    · obtain ⟨y, hy1, hy2⟩ := sq_Qd Y S1 S2 hS1 hS2 d h i c ⟨φ, hφ⟩
      change Qd _ d h i c (sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩) = plab χ L i c • sqMk Y S1 S2 hS1 hS2 ⟨φ, hφ⟩
      rw [hy2, ← map_smul, ← sub_eq_zero, ← map_sub, sqMk_zero]
      have := hq i c
      rw [← hy1] at this
      exact this
  have hne' : θq p0 (mkP ⟨φ, hφ⟩) ≠ 0 := by
    rw [hθq0]
    intro h0
    exact hne ((sqMk_zero Y' T1 T2 hT1 hT2 _).1 h0)
  obtain ⟨w, hw0, hwk, r, hwq⟩ := block_raise hS hT _ _ d h θq hθq χ L hL _ hv p0 hne'
  obtain ⟨ψ, rfl⟩ := sqMk_surj Y' T1 T2 hT1 hT2 w
  refine ⟨ψ.1, ψ.2, fun h0 => hw0 ((sqMk_zero Y' T1 T2 hT1 hT2 _).2 h0), fun p q hpq => ?_, r, fun i c => ?_, fun c => ?_⟩
  · have := hwk q p hpq
    rw [sq_E, sqMk_zero] at this
    exact this
  · obtain ⟨y, hy1, hy2⟩ := sq_Qd Y' T1 T2 hT1 hT2 d h i c ψ
    have := hwq i c
    rw [hy2, ← map_smul, ← sub_eq_zero, ← map_sub, sqMk_zero] at this
    rw [← hy1]
    exact this
  · have hQ := GlobalTheory.T.quantum_determinant_block_eigenvalue (sqMod Y' T1 T2 hT1 hT2) d h _ hwk (fun i c => plab (χ + Pi.single r 1) L i c) hwq c
    rw [prod_plab] at hQ
    have hc1 := hasChar_sub (trMod Y') T1 (fun a b φ hφ => hT1 b a φ hφ) (hasChar_tr Y' hchar)
    have hc2 : HasChar (sqMod Y' T1 T2 hT1 hT2) χ'' := hasChar_quo _ _ _ hc1
    obtain ⟨k, hkk⟩ := hc2
    have e := eigen_pow _ _ _ (Formalism.QuantumDeterminants.capP χ'' c) hQ k
    rw [hkk c] at e
    by_contra hne2
    have e' := e.symm
    exact hw0 ((smul_eq_zero.1 e').resolve_left (pow_ne_zero k (sub_ne_zero.2 hne2)))

section Step

variable (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (z : ℂ)

def comp0 (i : Fin n) : (step X z).V →ₗ[ℂ] X.V := (LinearMap.proj i) ∘ₗ (stepSub X z).subtype

def coordB (p : Fin n) : (step X z).V →ₗ[ℂ] X.V := ∑ a, B.Ui p a • comp0 X z a

/- English proof (translation)
Simplify using `[coordB, LinearMap.sum_apply]`.
-/
theorem coordB_apply (p : Fin n) (u : (step X z).V) : coordB X B z p u = ∑ a, B.Ui p a • comp0 X z a u := by
  simp [coordB, LinearMap.sum_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem component_zero_matrix_unit (i a b : Fin n) (u : (step X z).V) :
    comp0 X z i ((step X z).E a b u) = X.E a b (comp0 X z i u) + if i = a then comp0 X z b u else 0 := rfl

/- English proof (translation)
Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, component_zero_matrix_unit, smul_add, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `[smul_ite]`.
-/
theorem component_zero_matrix_action (i : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ) (u : (step X z).V) :
    comp0 X z i (actM (step X z).E Y u) = actM X.E Y (comp0 X z i u) + ∑ b, Y i b • comp0 X z b u := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, component_zero_matrix_unit, smul_add,
    Finset.sum_add_distrib]
  congr 1
  simp [smul_ite]

/- English proof (translation)
Establish `hY : ∀ i c, (B.U * Matrix.single b a 1 * B.Ui : Matrix (Fin n) (Fin n) ℂ) i c = B.U i b * B.Ui a c` using `fun i c => GlobalTheory.CompanionTheory.RgConjQdet.conj_single_apply _ _ _ _ _ _`. Establish `hd : ∑ i, B.Ui p i * B.U i b = if p = b then 1 else 0`. Use `congrFun (congrFun B.hUi p) b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`.

Rewrite using `[coordB_apply, coordB_apply]`. Simplify using `only [Eb, component_zero_matrix_action, smul_add, Finset.sum_add_distrib, map_sum, map_smul, hY]`. Use `congr 1`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Establish `: ∀ c, ∑ i, (B.Ui p i * (B.U i b * B.Ui a c)) • comp0 X z c u = (if p = b then B.Ui a c else 0) • comp0 X z c u`. Introduce `c`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring`. Apply the tactic sequence `_ = _ := by rw [hd]; split_ifs <;> simp`. Simplify using `only [this]`. Distinguish the cases in `hp : p = b`. Simplify using `[hp, coordB_apply]`.

Simplify using `[hp]`.
-/
theorem coordB_Eb (p a b : Fin n) (u : (step X z).V) :
    coordB X B z p (Eb (step X z) B b a u) = Eb X B b a (coordB X B z p u) + if p = b then coordB X B z a u else 0 := by
  have hY : ∀ i c, (B.U * Matrix.single b a 1 * B.Ui : Matrix (Fin n) (Fin n) ℂ) i c = B.U i b * B.Ui a c :=
    fun i c => GlobalTheory.CompanionTheory.RgConjQdet.conj_single_apply _ _ _ _ _ _
  have hd : ∑ i, B.Ui p i * B.U i b = if p = b then 1 else 0 := by
    have := congrFun (congrFun B.hUi p) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  rw [coordB_apply, coordB_apply]
  simp only [Eb, component_zero_matrix_action, smul_add, Finset.sum_add_distrib, map_sum, map_smul, hY]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ i, (B.Ui p i * (B.U i b * B.Ui a c)) • comp0 X z c u =
      (if p = b then B.Ui a c else 0) • comp0 X z c u := by
    intro c
    rw [← Finset.sum_smul]
    congr 1
    calc ∑ i, B.Ui p i * (B.U i b * B.Ui a c) = (∑ i, B.Ui p i * B.U i b) * B.Ui a c := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [hd]; split_ifs <;> simp
  simp only [this]
  by_cases hp : p = b
  · simp [hp, coordB_apply]
  · simp [hp]

end Step

def dI : Fin 3 → ℤ := ![-1, 0, 1]

/- English proof (translation)
Establish `hd : ∀ t, (![-1, 0, 1] : Fin 3 → ℂ) t = (dI t : ℂ)`. Apply the tactic sequence `intro t; fin_cases t <;> simp [dI]`. Use `set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1)) with hD`. Establish `hA : A = B.U * D * B.Ui` using `B.eq`. Establish `h1 : D * Matrix.single p q 1 = (dI (bl B p) : ℂ) • Matrix.single p q (1 : ℂ)`.

Use extensionality with `i c`. Distinguish the cases in `hi : i = p`. Substitute `hi` using the available equality. Simplify using `[hD, Matrix.diagonal_mul, Matrix.single_apply, hd, bl]`. Simplify using `[hD, Matrix.diagonal_mul, Matrix.single_apply, hi, Ne.symm hi]`.

Establish `h2 : Matrix.single p q 1 * D = (dI (bl B q) : ℂ) • Matrix.single p q (1 : ℂ)`. Use extensionality with `i c`. Distinguish the cases in `hc : c = q`. Substitute `hc` using the available equality. Simplify using `[hD, Matrix.mul_diagonal, Matrix.single_apply, hd, bl]`.

Simplify using `[hD, Matrix.mul_diagonal, Matrix.single_apply, hc, Ne.symm hc]`. Establish `e1 : A * (B.U * Matrix.single p q 1 * B.Ui) = B.U * (D * Matrix.single p q 1) * B.Ui`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (B.U * Matrix.single p q 1 * B.Ui) * A = B.U * (Matrix.single p q 1 * D) * B.Ui`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e1, e2, h1, h2]`. Use `push_cast`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, sub_smul]`.
-/
theorem grad_shift {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (p q : Fin n) :
    A * (B.U * Matrix.single p q 1 * B.Ui) - (B.U * Matrix.single p q 1 * B.Ui) * A =
      ((dI (bl B p) - dI (bl B q) : ℤ) : ℂ) • (B.U * Matrix.single p q 1 * B.Ui) := by
  have hd : ∀ t, (![-1, 0, 1] : Fin 3 → ℂ) t = (dI t : ℂ) := by
    intro t; fin_cases t <;> simp [dI]
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal
    (fun p => ((![-1, 0, 1] : Fin 3 → ℂ) ((stdBlocks (dims n B.j) B.hj).symm p).1)) with hD
  have hA : A = B.U * D * B.Ui := B.eq
  have h1 : D * Matrix.single p q 1 = (dI (bl B p) : ℂ) • Matrix.single p q (1 : ℂ) := by
    ext i c
    by_cases hi : i = p
    · subst hi; simp [hD, Matrix.diagonal_mul, Matrix.single_apply, hd, bl]
    · simp [hD, Matrix.diagonal_mul, Matrix.single_apply, hi, Ne.symm hi]
  have h2 : Matrix.single p q 1 * D = (dI (bl B q) : ℂ) • Matrix.single p q (1 : ℂ) := by
    ext i c
    by_cases hc : c = q
    · subst hc; simp [hD, Matrix.mul_diagonal, Matrix.single_apply, hd, bl]
    · simp [hD, Matrix.mul_diagonal, Matrix.single_apply, hc, Ne.symm hc]
  have e1 : A * (B.U * Matrix.single p q 1 * B.Ui) = B.U * (D * Matrix.single p q 1) * B.Ui := by
    calc A * (B.U * Matrix.single p q 1 * B.Ui) = B.U * D * B.Ui * (B.U * Matrix.single p q 1 * B.Ui) :=
          congrArg (fun T => T * (B.U * Matrix.single p q 1 * B.Ui)) hA
      _ = B.U * D * (B.Ui * B.U) * Matrix.single p q 1 * B.Ui := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [B.hUi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : (B.U * Matrix.single p q 1 * B.Ui) * A = B.U * (Matrix.single p q 1 * D) * B.Ui := by
    calc (B.U * Matrix.single p q 1 * B.Ui) * A = B.U * Matrix.single p q 1 * B.Ui * (B.U * D * B.Ui) :=
          congrArg (fun T => (B.U * Matrix.single p q 1 * B.Ui) * T) hA
      _ = B.U * Matrix.single p q 1 * (B.Ui * B.U) * D * B.Ui := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [B.hUi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, e2, h1, h2]
  push_cast
  simp only [Matrix.mul_smul, Matrix.smul_mul, sub_smul]

section Filt

variable {X : GMod n} {A : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Take `⟨s, hs⟩` from `hφ`. Use `⟨s - ((dI (bl B p) - dI (bl B q) : ℤ) : ℝ), fun u hu => ?_⟩` and prove the remaining obligations. Establish `h` using `F.shift _ _ (grad_shift B p q) _ u hu`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `hs _ h`.
-/
theorem W_Eb (F : Filt X A) (B : GradBasis A) (p q : Fin n) {φ : Module.Dual ℂ X.V} (hφ : φ ∈ W F) :
    (Eb X B p q).dualMap φ ∈ W F := by
  obtain ⟨s, hs⟩ := hφ
  refine ⟨s - ((dI (bl B p) - dI (bl B q) : ℤ) : ℝ), fun u hu => ?_⟩
  have h := F.shift _ _ (grad_shift B p q) _ u hu
  rw [sub_add_cancel] at h
  exact hs _ h

/- English proof (translation)
Establish `hM : (Matrix.single a b (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) = ∑ p, ∑ q, (B.Ui p a * B.U b q) • (B.U * Matrix.single p q 1 * B.Ui)`. Use extensionality with `i c`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.RgConjQdet.conj_single_apply]`. Establish `h1 : ∑ p, B.U i p * B.Ui p a = if i = a then 1 else 0`. Use `congrFun (congrFun B.hU i) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`. Establish `h2 : ∑ q, B.U b q * B.Ui q c = if b = c then 1 else 0`. Use `congrFun (congrFun B.hU b) c` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2, Matrix.single_apply]`. Apply the tactic sequence `by_cases e1 : a = i <;> by_cases e2 : b = c <;> simp [e1, e2, eq_comm]`. Use `_ = _ := by`.

Rewrite using `[Finset.sum_mul_sum]`. Conclude with `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring`. Rewrite using `[← actM_single X.E a b, hM]`. Express the relevant statement in the definitionally equal form `actML X.E _ = _`. Simplify using `only [map_sum, map_smul]`.

Both sides reduce to the same expression.
-/
theorem E_eq_sum (B : GradBasis A) (a b : Fin n) :
    X.E a b = ∑ p, ∑ q, (B.Ui p a * B.U b q) • Eb X B p q := by
  have hM : (Matrix.single a b (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ∑ p, ∑ q, (B.Ui p a * B.U b q) • (B.U * Matrix.single p q 1 * B.Ui) := by
    ext i c
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, GlobalTheory.CompanionTheory.RgConjQdet.conj_single_apply]
    have h1 : ∑ p, B.U i p * B.Ui p a = if i = a then 1 else 0 := by
      have := congrFun (congrFun B.hU i) a
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have h2 : ∑ q, B.U b q * B.Ui q c = if b = c then 1 else 0 := by
      have := congrFun (congrFun B.hU b) c
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    calc (Matrix.single a b (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) i c
        = (∑ p, B.U i p * B.Ui p a) * ∑ q, B.U b q * B.Ui q c := by
          rw [h1, h2, Matrix.single_apply]
          by_cases e1 : a = i <;> by_cases e2 : b = c <;> simp [e1, e2, eq_comm]
      _ = _ := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [← actM_single X.E a b, hM]
  change actML X.E _ = _
  simp only [map_sum, map_smul]
  rfl

/- English proof (translation)
Establish `e : (X.E a b).dualMap φ = ∑ p, ∑ q, (B.Ui p a * B.U b q) • (Eb X B p q).dualMap φ`. Express the relevant statement in the definitionally equal form `dualL X.V (X.E a b) φ = _`. Rewrite using `[E_eq_sum B a b]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (W_Eb F B p q hφ)`.
-/
theorem W_E (F : Filt X A) (B : GradBasis A) (a b : Fin n) {φ : Module.Dual ℂ X.V} (hφ : φ ∈ W F) :
    (X.E a b).dualMap φ ∈ W F := by
  have e : (X.E a b).dualMap φ = ∑ p, ∑ q, (B.Ui p a * B.U b q) • (Eb X B p q).dualMap φ := by
    change dualL X.V (X.E a b) φ = _
    rw [E_eq_sum B a b]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (W_Eb F B p q hφ)

end Filt

/- English proof (translation)
Establish `e : (actM X.E Y).dualMap φ = ∑ a, ∑ b, Y a b • (-(contraE X a b φ))`. Express the relevant statement in the definitionally equal form `dualL X.V (actM X.E Y) φ = _`. Simplify using `only [actM, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, contraE, LinearMap.neg_apply, neg_neg]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (T.neg_mem (hT a b φ hφ))`.
-/
theorem stable_act (X : GMod n) (T : Submodule ℂ (Module.Dual ℂ X.V)) (hT : ∀ a b, ∀ φ ∈ T, contraE X a b φ ∈ T)
    (Y : Matrix (Fin n) (Fin n) ℂ) {φ : Module.Dual ℂ X.V} (hφ : φ ∈ T) : (actM X.E Y).dualMap φ ∈ T := by
  have e : (actM X.E Y).dualMap φ = ∑ a, ∑ b, Y a b • (-(contraE X a b φ)) := by
    change dualL X.V (actM X.E Y) φ = _
    simp only [actM, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, contraE, LinearMap.neg_apply, neg_neg]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (T.neg_mem (hT a b φ hφ))

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Use `⟨k, fun c => ?_⟩` and prove the remaining obligations. Establish `e : qdet (ebMod X B).E (c + ((n : ℂ) - 1) / 2) = qdet X.E (c + ((n : ℂ) - 1) / 2)` using `GlobalTheory.CompanionTheory.RgConjQdet.conjQdet n X B.U B.Ui B.hU B.hUi _`. Conclude with `(congrArg (fun T : Module.End ℂ X.V => (T - Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ X.V)) ^ k) e).trans (hk c)`.
-/
theorem hasChar_eb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) {χ : Fin n → ℂ} (h : HasChar X χ) :
    HasChar (ebMod X B) χ := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun c => ?_⟩
  have e : qdet (ebMod X B).E (c + ((n : ℂ) - 1) / 2) = qdet X.E (c + ((n : ℂ) - 1) / 2) :=
    GlobalTheory.CompanionTheory.RgConjQdet.conjQdet n X B.U B.Ui B.hU B.hUi _
  exact (congrArg (fun T : Module.End ℂ X.V => (T - Formalism.QuantumDeterminants.capP χ c • (1 : Module.End ℂ X.V)) ^ k) e).trans (hk c)

/- English proof (translation)
Set `f : S →ₗ[ℂ] V ⧸ M` to `M.mkQ ∘ₗ S.subtype`. Establish `hψ : ψ ∈ LinearMap.range f.dualMap`. Rewrite using `[LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]`. Introduce `u hu`. Use `h u ?_` and prove the remaining obligations.

Establish `: M.mkQ (u : V) = 0` using `hu`. Simplify using `using this`. Take `⟨g, rfl⟩` from `hψ`. Use `⟨g ∘ₗ M.mkQ, fun u => rfl, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: M.mkQ x = 0` using `by simpa using hx`.

Simplify using `[this]`.
-/
theorem exists_ext {V : Type} [AddCommGroup V] [Module ℂ V] (S M : Submodule ℂ V) (ψ : Module.Dual ℂ S)
    (h : ∀ u : S, (u : V) ∈ M → ψ u = 0) :
    ∃ Ψ : Module.Dual ℂ V, (∀ u : S, Ψ u = ψ u) ∧ ∀ x ∈ M, Ψ x = 0 := by
  let f : S →ₗ[ℂ] V ⧸ M := M.mkQ ∘ₗ S.subtype
  have hψ : ψ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro u hu
    refine h u ?_
    have : M.mkQ (u : V) = 0 := hu
    simpa using this
  obtain ⟨g, rfl⟩ := hψ
  refine ⟨g ∘ₗ M.mkQ, fun u => rfl, fun x hx => ?_⟩
  have : M.mkQ x = 0 := by simpa using hx
  simp [this]

/- English proof (translation)
Introduce `hS hT n X A F B χ s F'' Λ hchar _ hsand hPP W'' hle hstab hne`. Establish `hT2 : ∀ a b, ∀ ψ ∈ W'', ((step X (χ s)).E a b).dualMap ψ ∈ W''` using `fun a b ψ hψ => by`. Use `W''.neg_mem (hstab a b ψ hψ)` as an intermediate fact. Simplify `this` using `[contraE]`. Set `Z : Submodule ℂ (Module.Dual ℂ X.V)` to `W F ⊓ ⨅ i, W''.comap (comp0 X (χ s) i).dualMap`.

Establish `hZmem : ∀ φ, φ ∈ Z ↔ φ ∈ W F ∧ ∀ i, (comp0 X (χ s) i).dualMap φ ∈ W''` using `fun φ => by`. Simplify using `[Z, Submodule.mem_inf, Submodule.mem_iInf]`. Establish `hcompW : ∀ i, ∀ φ ∈ W F, (comp0 X (χ s) i).dualMap φ ∈ W F''`. Introduce and unpack `i φ ⟨t, ht⟩`. Use `⟨t - 1, fun u hu => ht _ ?_⟩` and prove the remaining obligations.

Use `(hsand (t - 1) u).2 hu i` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hZle : Z ≤ W F` using `fun φ hφ => ((hZmem φ).1 hφ).1`. Establish `hZE : ∀ a b, ∀ φ ∈ Z, (X.E a b).dualMap φ ∈ Z`. Introduce `a b φ hφ`.

Take `⟨h1, h2⟩` from `(hZmem φ).1 hφ`. Use `(hZmem _).2 ⟨W_E F B a b h1, fun i => ?_⟩` and prove the remaining obligations. Establish `e : (comp0 X (χ s) i).dualMap ((X.E a b).dualMap φ) = ((step X (χ s)).E a b).dualMap ((comp0 X (χ s) i).dualMap φ) - if i = a then (comp0 X (χ s) b).dualMap φ else 0`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = a`.

Simplify using `[LinearMap.dualMap_apply, component_zero_matrix_unit, hi]`. Simplify using `[LinearMap.dualMap_apply, component_zero_matrix_unit, hi]`. Rewrite using `[e]`. Use `W''.sub_mem (hT2 a b _ (h2 i)) ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `h2 b`. Conclude with `W''.zero_mem`. Establish `hZst : ∀ a b, ∀ φ ∈ Z, contraE X a b φ ∈ Z` using `fun a b φ hφ => by`. Use `Z.neg_mem (hZE a b φ hφ)` as an intermediate fact. Simplify `this` using `[contraE]`.

Establish `hZne : Z ≠ W F`. Introduce `hZ`. Use `hne (le_antisymm hle ?_)` and prove the remaining obligations. Introduce and unpack `ψ ⟨t, ht⟩`. Set `M : Submodule ℂ (Fin n → X.V)` to `Submodule.pi Set.univ fun _ => F.N (t - 1)`.

Take `⟨Ψ, hΨ1, hΨ2⟩` from `exists_ext (stepSub X (χ s)) M ψ (fun u hu => ht u ((hsand t u).1 fun i => hu i (Set.mem_univ _)))`. Establish `hmem : ∀ i, Ψ ∘ₗ LinearMap.single ℂ (fun _ => X.V) i ∈ Z`. Introduce `i`. Rewrite using `[hZ]`. Use `⟨t - 1, fun x hx => hΨ2 _ fun j _ => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`. Simplify `(F.N (t - 1)).zero_mem` using `[hj]`. Establish `e : ψ = ∑ i, (comp0 X (χ s) i).dualMap (Ψ ∘ₗ LinearMap.single ℂ (fun _ => X.V) i)`.

Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Use `(hΨ1 u).symm.trans ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.dualMap_apply, LinearMap.comp_apply]`. Rewrite using `[← map_sum]`.

Use `congrArg Ψ ?_` and prove the remaining obligations. Set `u' : stepSub X (χ s)` to `u`. Conclude with `(Finset.univ_sum_single (u' : Fin n → X.V)).symm`. Rewrite using `[e]`. Conclude with `W''.sum_mem fun i _ => ((hZmem _).1 (hmem i)).2 i`.

Take `⟨φ, hφ, hφZ, hkill, L, hLΛ, hLab, hQ⟩` from `hPP Z hZle hZst hZne`. Set `θ : Fin n → Module.Dual ℂ X.V →ₗ[ℂ] Module.Dual ℂ (step X (χ s)).V` to `fun p => (coordB X B (χ s) p).dualMap`. Establish `hθsum : ∀ p φ, θ p φ = ∑ a, B.Ui p a • (comp0 X (χ s) a).dualMap φ`. Introduce `p φ`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations.

Simplify using `[θ, LinearMap.dualMap_apply, coordB_apply, LinearMap.sum_apply]`. Establish `hcomp : ∀ i φ, (comp0 X (χ s) i).dualMap φ = ∑ p, B.U i p • θ p φ`. Introduce `i φ`. Establish `h1 : ∀ c, ∑ p, B.U i p * B.Ui p c = if i = c then 1 else 0` using `fun c => by`. Use `congrFun (congrFun B.hU i) c` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Conclude with `this`. Simplify using `only [hθsum, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, h1]`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨p0, hp0⟩ : ∃ p, θ p φ ∉ W'' := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `hφZ ((hZmem φ).2 ⟨hφ, fun i => ?_⟩)` and prove the remaining obligations.

Rewrite using `[hcomp]`. Conclude with `W''.sum_mem fun p _ => W''.smul_mem _ (hc p)`. Establish `hθE : ∀ a b p φ, (Eb (step X (χ s)) B b a).dualMap (θ p φ) = θ p ((Eb X B b a).dualMap φ) + if p = b then θ a φ else 0`. Introduce `a b p φ`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations.

Establish `e` using `coordB_Eb X B (χ s) p a b u`. Distinguish the cases in `hp : p = b`. Rewrite using `[if_pos hp]`. Express the relevant statement in the definitionally equal form `φ (coordB X B (χ s) p (Eb (step X (χ s)) B b a u)) = φ (Eb X B b a (coordB X B (χ s) p u)) + φ (coordB X B (χ s) a u)`. Rewrite using `[e, if_pos hp, map_add]`.

Rewrite using `[if_neg hp, add_zero]`. Express the relevant statement in the definitionally equal form `φ (coordB X B (χ s) p (Eb (step X (χ s)) B b a u)) = φ (Eb X B b a (coordB X B (χ s) p u))`. Rewrite using `[e, if_neg hp, add_zero]`. Establish `hθW : ∀ p, ∀ φ ∈ W F, θ p φ ∈ W F''` using `fun p φ hφ => by`. Rewrite using `[hθsum]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hcompW a φ hφ)`. Establish `hθZ : ∀ p, ∀ φ ∈ Z, θ p φ ∈ W''` using `fun p φ hφ => by`. Rewrite using `[hθsum]`. Conclude with `W''.sum_mem fun a _ => W''.smul_mem _ (((hZmem φ).1 hφ).2 a)`. Establish `hchar'` using `hasChar_eb (step X (χ s)) B (hS n X χ s hchar)`.

Take `⟨ψ, hψ1, hψ2, hψk, r, hψq, hcap⟩` from `sub_raise hS hT (ebMod X B) (ebMod (step X (χ s)) B) (dims n B.j) B.hj (W (X := X) F) Z (W (X := step X (χ s)) F'') W'' (fun a b φ hφ => W_Eb F B a b hφ) (fun a b φ hφ => stable_act X Z hZst _ hφ) (fun a b φ hφ => W_Eb F'' B a b hφ) (fun a b ψ hψ => stable_act _ W'' hstab _ hψ) θ …`. Establish `hr : χ r = χ s` using `entry_eq_of_capP χ r s hcap`. Use `⟨ψ, hψ1, hψ2, hψk, L ∘ Equiv.swap r s, ⟨L, hLΛ, r, hr, rfl⟩, isLabel_swap hLab r s, fun i Y => ?_⟩` and prove the remaining obligations. Rewrite using `[plab_swap χ L r s hr]`. Conclude with `hψq i Y`.
-/
theorem transport : Transport := by
  intro hS hT n X A F B χ s F'' Λ hchar _ hsand hPP W'' hle hstab hne
  have hT2 : ∀ a b, ∀ ψ ∈ W'', ((step X (χ s)).E a b).dualMap ψ ∈ W'' := fun a b ψ hψ => by
    have := W''.neg_mem (hstab a b ψ hψ)
    simpa [contraE] using this

  let Z : Submodule ℂ (Module.Dual ℂ X.V) := W F ⊓ ⨅ i, W''.comap (comp0 X (χ s) i).dualMap
  have hZmem : ∀ φ, φ ∈ Z ↔ φ ∈ W F ∧ ∀ i, (comp0 X (χ s) i).dualMap φ ∈ W'' := fun φ => by
    simp [Z, Submodule.mem_inf, Submodule.mem_iInf]
  have hcompW : ∀ i, ∀ φ ∈ W F, (comp0 X (χ s) i).dualMap φ ∈ W F'' := by
    rintro i φ ⟨t, ht⟩
    refine ⟨t - 1, fun u hu => ht _ ?_⟩
    have := (hsand (t - 1) u).2 hu i
    rwa [sub_add_cancel] at this
  have hZle : Z ≤ W F := fun φ hφ => ((hZmem φ).1 hφ).1
  have hZE : ∀ a b, ∀ φ ∈ Z, (X.E a b).dualMap φ ∈ Z := by
    intro a b φ hφ
    obtain ⟨h1, h2⟩ := (hZmem φ).1 hφ
    refine (hZmem _).2 ⟨W_E F B a b h1, fun i => ?_⟩
    have e : (comp0 X (χ s) i).dualMap ((X.E a b).dualMap φ) =
        ((step X (χ s)).E a b).dualMap ((comp0 X (χ s) i).dualMap φ) -
          if i = a then (comp0 X (χ s) b).dualMap φ else 0 := by
      refine LinearMap.ext fun u => ?_
      by_cases hi : i = a
      · simp [LinearMap.dualMap_apply, component_zero_matrix_unit, hi]
      · simp [LinearMap.dualMap_apply, component_zero_matrix_unit, hi]
    rw [e]
    refine W''.sub_mem (hT2 a b _ (h2 i)) ?_
    split_ifs
    · exact h2 b
    · exact W''.zero_mem
  have hZst : ∀ a b, ∀ φ ∈ Z, contraE X a b φ ∈ Z := fun a b φ hφ => by
    have := Z.neg_mem (hZE a b φ hφ)
    simpa [contraE] using this
  have hZne : Z ≠ W F := by
    intro hZ
    refine hne (le_antisymm hle ?_)
    rintro ψ ⟨t, ht⟩
    let M : Submodule ℂ (Fin n → X.V) := Submodule.pi Set.univ fun _ => F.N (t - 1)
    obtain ⟨Ψ, hΨ1, hΨ2⟩ := exists_ext (stepSub X (χ s)) M ψ (fun u hu =>
      ht u ((hsand t u).1 fun i => hu i (Set.mem_univ _)))
    have hmem : ∀ i, Ψ ∘ₗ LinearMap.single ℂ (fun _ => X.V) i ∈ Z := by
      intro i
      rw [hZ]
      refine ⟨t - 1, fun x hx => hΨ2 _ fun j _ => ?_⟩
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [hj] using (F.N (t - 1)).zero_mem
    have e : ψ = ∑ i, (comp0 X (χ s) i).dualMap (Ψ ∘ₗ LinearMap.single ℂ (fun _ => X.V) i) := by
      refine LinearMap.ext fun u => ?_
      refine (hΨ1 u).symm.trans ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.dualMap_apply, LinearMap.comp_apply]
      rw [← map_sum]
      refine congrArg Ψ ?_
      let u' : stepSub X (χ s) := u
      exact (Finset.univ_sum_single (u' : Fin n → X.V)).symm
    rw [e]
    exact W''.sum_mem fun i _ => ((hZmem _).1 (hmem i)).2 i
  obtain ⟨φ, hφ, hφZ, hkill, L, hLΛ, hLab, hQ⟩ := hPP Z hZle hZst hZne
  let θ : Fin n → Module.Dual ℂ X.V →ₗ[ℂ] Module.Dual ℂ (step X (χ s)).V := fun p => (coordB X B (χ s) p).dualMap
  have hθsum : ∀ p φ, θ p φ = ∑ a, B.Ui p a • (comp0 X (χ s) a).dualMap φ := by
    intro p φ
    refine LinearMap.ext fun u => ?_
    simp [θ, LinearMap.dualMap_apply, coordB_apply, LinearMap.sum_apply]
  have hcomp : ∀ i φ, (comp0 X (χ s) i).dualMap φ = ∑ p, B.U i p • θ p φ := by
    intro i φ
    have h1 : ∀ c, ∑ p, B.U i p * B.Ui p c = if i = c then 1 else 0 := fun c => by
      have := congrFun (congrFun B.hU i) c
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    simp only [hθsum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, h1]
    simp
  obtain ⟨p0, hp0⟩ : ∃ p, θ p φ ∉ W'' := by
    by_contra hc
    push_neg at hc
    refine hφZ ((hZmem φ).2 ⟨hφ, fun i => ?_⟩)
    rw [hcomp]
    exact W''.sum_mem fun p _ => W''.smul_mem _ (hc p)
  have hθE : ∀ a b p φ, (Eb (step X (χ s)) B b a).dualMap (θ p φ) =
      θ p ((Eb X B b a).dualMap φ) + if p = b then θ a φ else 0 := by
    intro a b p φ
    refine LinearMap.ext fun u => ?_
    have e := coordB_Eb X B (χ s) p a b u
    by_cases hp : p = b
    · rw [if_pos hp]
      change φ (coordB X B (χ s) p (Eb (step X (χ s)) B b a u)) =
        φ (Eb X B b a (coordB X B (χ s) p u)) + φ (coordB X B (χ s) a u)
      rw [e, if_pos hp, map_add]
    · rw [if_neg hp, add_zero]
      change φ (coordB X B (χ s) p (Eb (step X (χ s)) B b a u)) = φ (Eb X B b a (coordB X B (χ s) p u))
      rw [e, if_neg hp, add_zero]
  have hθW : ∀ p, ∀ φ ∈ W F, θ p φ ∈ W F'' := fun p φ hφ => by
    rw [hθsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hcompW a φ hφ)
  have hθZ : ∀ p, ∀ φ ∈ Z, θ p φ ∈ W'' := fun p φ hφ => by
    rw [hθsum]
    exact W''.sum_mem fun a _ => W''.smul_mem _ (((hZmem φ).1 hφ).2 a)
  have hchar' := hasChar_eb (step X (χ s)) B (hS n X χ s hchar)
  obtain ⟨ψ, hψ1, hψ2, hψk, r, hψq, hcap⟩ := sub_raise hS hT (ebMod X B) (ebMod (step X (χ s)) B) (dims n B.j) B.hj
    (W (X := X) F) Z (W (X := step X (χ s)) F'') W'' (fun a b φ hφ => W_Eb F B a b hφ)
    (fun a b φ hφ => stable_act X Z hZst _ hφ)
    (fun a b φ hφ => W_Eb F'' B a b hφ) (fun a b ψ hψ => stable_act _ W'' hstab _ hψ)
    θ hθE hθW hθZ
    χ L hLab φ hφ hkill hQ p0 hp0 _ hchar'
  have hr : χ r = χ s := entry_eq_of_capP χ r s hcap
  refine ⟨ψ, hψ1, hψ2, hψk, L ∘ Equiv.swap r s, ⟨L, hLΛ, r, hr, rfl⟩, isLabel_swap hLab r s, fun i Y => ?_⟩
  rw [plab_swap χ L r s hr]
  exact hψq i Y

end GlobalTheory.CompanionTheory.RgTransport
