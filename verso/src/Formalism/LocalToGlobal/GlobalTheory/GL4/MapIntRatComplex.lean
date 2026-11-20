import Formalism.LocalToGlobal.GlobalTheory.GL4.ApplyWordMemDualGen
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

def dpowR (R : Type) [CommRing R] (n c : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  lpMinor R (r := n) (n := n) n le_rfl le_rfl ^ c

/- English proof (translation)
Unfold `dpowR`. Rewrite using `[map_pow, lclosedeq_lpMinor_map]`.
-/
theorem map_dpowR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n c : ℕ) :
    map φ (dpowR R n c) = dpowR S n c := by
  unfold dpowR
  rw [map_pow, lclosedeq_lpMinor_map]

/- English proof (translation)
Rewrite using `[sgNat_eq lt sg h0 hI]`. Consider the cases of `n with`. Consider the case `zero`. Establish `hc : sg.detShift.toNat = 0` using `by unfold DomWeight.detShift; simp`. Establish `hf : (fun i : Fin 0 => sg.natW i + 0) = sg.natW` using `funext fun i => i.elim0`.

Simplify using `only [hc, hf]`. Simplify using `[dpowR]`. Consider the case `succ m => exact fun v hv => det_mul_mem_weyl R sg.natW _ v hv`.
-/
theorem twist_mem_gen (R : Type) [CommRing R] {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n)
    (h0 : lt.w (Fin.last n) = 0) (hI : Interlace lt sg) :
    ∀ v ∈ weyl R n n le_rfl sg.natW, dpowR R n sg.detShift.toNat * v ∈ weyl R n n le_rfl (sgNat sg) := by
  rw [sgNat_eq lt sg h0 hI]
  cases n with
  | zero =>
    have hc : sg.detShift.toNat = 0 := by unfold DomWeight.detShift; simp
    have hf : (fun i : Fin 0 => sg.natW i + 0) = sg.natW := funext fun i => i.elim0
    simp only [hc, hf]
    simp [dpowR]
  | succ m => exact fun v hv => det_mul_mem_weyl R sg.natW _ v hv

/- English proof (translation)
Unfold `weyl at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`. Use `⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.cast_one, one_smul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Consider the case `zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨N1, h1, y1, hy1, e1⟩` from `ihx`. Take `⟨N2, h2, y2, hy2, e2⟩` from `ihy`.

Use `⟨N1 * N2, mul_ne_zero h1 h2, N2 • y1 + N1 • y2, Submodule.add_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hy2), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul_gen, map_smul_gen, ← e1, ← e2, smul_add, smul_smul, smul_smul, eq_intCast, eq_intCast, Int.cast_mul, mul_comm (N2 : ℚ)]`. Consider the case `smul c x _ ihx`. Take `⟨N1, h1, y1, hy1, e1⟩` from `ihx`. Use `⟨(c.den : ℤ) * N1, mul_ne_zero (by exact_mod_cast c.den_ne_zero) h1, c.num • y1, Submodule.smul_mem _ _ hy1, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul_gen, ← e1, smul_smul, smul_smul, eq_intCast]`. Use `congr 1`. Use `Rat.den_mul_eq_num c` as an intermediate fact. Use `push_cast`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem weylQ_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (x : MvPolynomial (Fin r × Fin n) ℚ)
    (hx : x ∈ weyl ℚ r n hn ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ y ∈ weyl ℤ r n hn ν, (N : ℚ) • x = map (Int.castRingHom ℚ) y := by
  unfold weyl at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [Int.cast_one, one_smul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1, y1, hy1, e1⟩ := ihx
    obtain ⟨N2, h2, y2, hy2, e2⟩ := ihy
    refine ⟨N1 * N2, mul_ne_zero h1 h2, N2 • y1 + N1 • y2,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hy2), ?_⟩
    rw [map_add, map_smul_gen, map_smul_gen, ← e1, ← e2, smul_add, smul_smul, smul_smul, eq_intCast, eq_intCast,
      Int.cast_mul, mul_comm (N2 : ℚ)]
  | smul c x _ ihx =>
    obtain ⟨N1, h1, y1, hy1, e1⟩ := ihx
    refine ⟨(c.den : ℤ) * N1, mul_ne_zero (by exact_mod_cast c.den_ne_zero) h1, c.num • y1,
      Submodule.smul_mem _ _ hy1, ?_⟩
    rw [map_smul_gen, ← e1, smul_smul, smul_smul, eq_intCast]
    congr 1
    have := Rat.den_mul_eq_num c
    push_cast
    rw [← this]
    ring

/- English proof (translation)
Establish `h1 : map (Int.castRingHom ℚ) q ∈ weyl ℚ r n hn ν`. Rewrite using `[Formalism.GradedWeylDivisibility.weylEqNablaQ r n hn ν hν]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ r n ν q hq`. Take `⟨N, hN, y, hy, e⟩` from `weylQ_denom hn ν _ h1`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations.

Establish `: N • q = y`. Apply `map_injective (Int.castRingHom ℚ) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[map_smul_gen, eq_intCast, e]`. Rewrite using `[this]`. Conclude with `hy`.
-/
theorem nablaZ_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (q : MvPolynomial (Fin r × Fin n) ℤ)
    (hq : q ∈ dualWeyl ℤ r n ν) : ∃ N : ℤ, N ≠ 0 ∧ N • q ∈ weyl ℤ r n hn ν := by
  have h1 : map (Int.castRingHom ℚ) q ∈ weyl ℚ r n hn ν := by
    rw [Formalism.GradedWeylDivisibility.weylEqNablaQ r n hn ν hν]
    exact Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ r n ν q hq
  obtain ⟨N, hN, y, hy, e⟩ := weylQ_denom hn ν _ h1
  refine ⟨N, hN, ?_⟩
  have : N • q = y := by
    apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_smul_gen, eq_intCast, e]
  rw [this]
  exact hy

def fockQLin {κ : Type} (G : MvPolynomial κ ℚ) : MvPolynomial κ ℚ →ₗ[ℚ] ℚ where
  toFun F := fockQ F G
  map_add' F F' := (Formalism.GradedWeylDivisibility.fockQBilin κ F F' G 0).1
  map_smul' c F := by rw [(Formalism.GradedWeylDivisibility.fockQBilin κ F 0 G c).2, smul_eq_mul, RingHom.id_apply]

/- English proof (translation)
The claim follows from `(Formalism.GradedWeylDivisibility.fockQPos κ f g).1`.
-/
theorem fockQ_comm {κ : Type} (f g : MvPolynomial κ ℚ) : fockQ f g = fockQ g f := (Formalism.GradedWeylDivisibility.fockQPos κ f g).1

/- English proof (translation)
Set `B : V →ₗ[ℚ] Module.Dual ℚ V` to `{ toFun := fun x => (fockQLin (x : MvPolynomial κ ℚ)).comp V.subtype map_add' := by`. Introduce `x y`. Use extensionality with `v`. Use `show fockQ (v : MvPolynomial κ ℚ) ((x : MvPolynomial κ ℚ) + y) = fockQ (v : MvPolynomial κ ℚ) x + fockQ (v : MvPolynomial κ ℚ) y`. Rewrite using `[fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ _ _ 0).1, fockQ_comm, fockQ_comm (y : MvPolynomial κ ℚ)]`.

Use the proof step `map_smul' := by`. Introduce `c x`. Use extensionality with `v`. Use `show fockQ (v : MvPolynomial κ ℚ) (c • (x : MvPolynomial κ ℚ)) = c * fockQ (v : MvPolynomial κ ℚ) x`. Rewrite using `[fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ 0 _ c).2, fockQ_comm] }`.

Establish `hB : ∀ x v : V, B x v = fockQ (v : MvPolynomial κ ℚ) (x : MvPolynomial κ ℚ)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective B`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Assume the negation of the conclusion as `hne`.

Establish `hne' : (x : MvPolynomial κ ℚ) ≠ 0` using `fun h => hne (Subtype.ext h)`. Establish `hpos` using `(Formalism.GradedWeylDivisibility.fockQPos κ (x : MvPolynomial κ ℚ) x).2 hne'`. Establish `: B x x = 0` using `by rw [hx]; rfl`. Rewrite `this` using `[hB]`. Conclude with `hpos.ne' this`.

Establish `hsurj : Function.Surjective B` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hinj`. Take `⟨p, hp⟩` from `hsurj φ`. Use `⟨p, p.2, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← hp, hB, fockQ_comm]`.
-/
theorem rieszQ {κ : Type} (V : Submodule ℚ (MvPolynomial κ ℚ)) [FiniteDimensional ℚ V] (φ : V →ₗ[ℚ] ℚ) :
    ∃ p ∈ V, ∀ v : V, fockQ p (v : MvPolynomial κ ℚ) = φ v := by
  let B : V →ₗ[ℚ] Module.Dual ℚ V :=
    { toFun := fun x => (fockQLin (x : MvPolynomial κ ℚ)).comp V.subtype
      map_add' := by
        intro x y
        ext v
        show fockQ (v : MvPolynomial κ ℚ) ((x : MvPolynomial κ ℚ) + y) = fockQ (v : MvPolynomial κ ℚ) x + fockQ (v : MvPolynomial κ ℚ) y
        rw [fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ _ _ 0).1, fockQ_comm, fockQ_comm (y : MvPolynomial κ ℚ)]
      map_smul' := by
        intro c x
        ext v
        show fockQ (v : MvPolynomial κ ℚ) (c • (x : MvPolynomial κ ℚ)) = c * fockQ (v : MvPolynomial κ ℚ) x
        rw [fockQ_comm, (Formalism.GradedWeylDivisibility.fockQBilin κ _ 0 _ c).2, fockQ_comm] }
  have hB : ∀ x v : V, B x v = fockQ (v : MvPolynomial κ ℚ) (x : MvPolynomial κ ℚ) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hne' : (x : MvPolynomial κ ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (Formalism.GradedWeylDivisibility.fockQPos κ (x : MvPolynomial κ ℚ) x).2 hne'
    have : B x x = 0 := by rw [hx]; rfl
    rw [hB] at this
    exact hpos.ne' this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨p, hp⟩ := hsurj φ
  refine ⟨p, p.2, fun v => ?_⟩
  rw [← hp, hB, fockQ_comm]

/- English proof (translation)
The claim follows from `(Formalism.GradedWeylDivisibility.fockQPos _ _ (hw ℚ hn ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ r n hn ν)`.
-/
theorem fockQ_hw_pos {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : 0 < fockQ (hw ℚ hn ν) (hw ℚ hn ν) :=
  (Formalism.GradedWeylDivisibility.fockQPos _ _ (hw ℚ hn ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ r n hn ν)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intQ_apply (r n : ℕ) (q : MvPolynomial (Fin r × Fin n) ℤ) : intQ r n q = map (Int.castRingHom ℚ) q := rfl

/- English proof (translation)
Rewrite using `[map_map]`. Use `congr 1`.
-/
theorem map_int_rat_complex {κ : Type} (g : MvPolynomial κ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [map_map]
  congr 1

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
