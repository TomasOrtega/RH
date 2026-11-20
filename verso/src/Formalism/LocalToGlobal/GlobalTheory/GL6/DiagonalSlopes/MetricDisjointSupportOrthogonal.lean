import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeRamifiedInducedPrimeField
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Establish `hle : RatSpan D lam ≤ (MvPolynomial.map D.what₂.embLL : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL →+* MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ).range.toAddSubgroup`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, f, -, rfl⟩`. Use `⟨r • ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]`.

Use `congr 1`. Simplify using `only [ten, map_prod, MvPolynomial.map_rename, MvPolynomial.map_map, RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]`. Take `⟨Q, hQ⟩` from `hle hP`. Conclude with `⟨Q, hQ⟩`.
-/
theorem rational_span_map_surjective {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hP : P ∈ RatSpan D lam) :
    ∃ Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL Q = P := by
  have hle : RatSpan D lam ≤
      (MvPolynomial.map D.what₂.embLL : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL →+*
        MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ).range.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨r, f, -, rfl⟩
    refine ⟨r • ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    simp only [ten, map_prod, MvPolynomial.map_rename, MvPolynomial.map_map,
      RingHom.ext_int (D.what₂.embLL.comp (Int.castRingHom D.what₂.LL)) (Int.castRingHom ℂ)]
  obtain ⟨Q, hQ⟩ := hle hP
  exact ⟨Q, hQ⟩

/- English proof (translation)
Establish `hr` using `((Tf.val 0 (Nat.zero_le _) rfl).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩`. Use `choose P hP hPe using hr.2`. Use `choose Q hQ using fun c => rational_span_map_surjective _ (P c) (hP c)`. Use `⟨fun c => if (D.fm u).emb 0 x c = 0 then 0 else Q c, fun c h => by simp [h], fun c z => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : (D.fm u).emb 0 x c = 0`.

Rewrite using `[h]`. Simplify using `only [h, if_true, map_zero, Pi.zero_apply]`. Simplify using `only [h, if_false, hQ]`. Conclude with `hPe c z`.
-/
theorem polynomial_rep_of_rational_form (Tf : Forms0 D u) (x : ((D.fm u).lat 0).V) :
    ∃ Pc : (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL,
      (∀ c, (D.fm u).emb 0 x c = 0 → Pc c = 0) ∧
      ∀ c z, (D.fm u).emb 0 x c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val 0 (Nat.zero_le _) rfl).eY z) := by
  have hr := ((Tf.val 0 (Nat.zero_le _) rfl).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  choose P hP hPe using hr.2
  choose Q hQ using fun c => rational_span_map_surjective _ (P c) (hP c)
  refine ⟨fun c => if (D.fm u).emb 0 x c = 0 then 0 else Q c, fun c h => by simp [h], fun c z => ?_⟩
  by_cases h : (D.fm u).emb 0 x c = 0
  · rw [h]
    simp only [h, if_true, map_zero, Pi.zero_apply]
  · simp only [h, if_false, hQ]
    exact hPe c z

/- English proof (translation)
Simplify using `[nfAll, Formalism.REAL.fockF]`.
-/
theorem norm_form_zero {n : ℕ} (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

/- English proof (translation)
Unfold `majAt`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, RCLike.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem majAt_swap_eq_conj {V ι : Type} [AddCommGroup V] [Module D.what₂.LL V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι D.what₂.LL V)
    (X : InfinitePlace D.what₂.LL → Matrix ι ι ℂ) (v : InfinitePlace D.what₂.LL) (x y : V) :
    majAt b X v y x = starRingEnd ℂ (majAt b X v x y) := by
  unfold majAt
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, RCLike.star_def, Complex.conj_conj]
  ring

/- English proof (translation)
Introduce `v x y hxy`. Use `set s := v.embedding with hs`. Establish `hv : InfinitePlace.mk s = v` using `InfinitePlace.mk_embedding v`. Take `⟨C, hC, -, -⟩` from `(Tf.val 0 (Nat.zero_le _) rfl).de`. Use `letI := D.host.cmStar`.

Take `⟨o, ho⟩` from `exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC`. Take `⟨Px, hPx0, hPx⟩` from `polynomial_rep_of_rational_form Tf x`. Take `⟨Py, hPy0, hPy⟩` from `polynomial_rep_of_rational_form Tf y`. Establish `hay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (a • y) c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (MvPolynomial.C a * Py c)) ((Tf.val 0 (Nat.zero_le _) rfl).eY z)`. Introduce `a c z`.

Rewrite using `[map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hPy, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_smul, Pi.smul_apply]`. Establish `hxay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (x + a • y) c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Px c + MvPolynomial.C a * Py c)) ((Tf.val 0 (Nat.zero_le _) rfl).eY z)`. Introduce `a c z`. Rewrite using `[map_add, Pi.add_apply, Pi.add_apply, hPx, hay, map_add, map_add, Pi.add_apply]`. Establish `key : ∀ a : D.what₂.LL, (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + a • y) (x + a • y)).re = (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re + (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (a • y) (a • y)).re`.

Introduce `a`. Establish `e1` using `Tf.norm 0 (Nat.zero_le _) rfl s (x + a • y) _ (hxay a) o ho`. Establish `e2` using `Tf.norm 0 (Nat.zero_le _) rfl s x Px hPx o ho`. Establish `e3` using `Tf.norm 0 (Nat.zero_le _) rfl s (a • y) _ (hay a) o ho`. Rewrite `e1`, `e2`, `e3` using `[hv]`.

Rewrite using `[e1, e2, e3, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Break down `hxy c with h | h` into its components or cases. Rewrite using `[hPx0 c h]`. Simplify using `only [zero_add, map_zero, norm_form_zero, Complex.zero_re, mul_zero]`.

Rewrite using `[hPy0 c h]`. Simplify using `only [mul_zero, add_zero, map_zero, norm_form_zero, Complex.zero_re]`. Establish `a1 : ∀ x x' y : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + x') y = majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x' y` using `(isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).1`. Establish `a2 : ∀ x y y' : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (y + y') = majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y'` using `(isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.1`. Establish `s2 : ∀ (a : D.what₂.LL) (x y : ((D.fm u).lat 0).V), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y) = s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y` using `(isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.2.2`.

Establish `hre : ∀ a : D.what₂.LL, (s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y).re = 0`. Introduce `a`. Establish `k` using `key a`. Rewrite `k` using `[a1, a2, a2, majAt_swap_eq_conj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y)]`. Rewrite `k` using `[s2]`.

Simplify using `only [Complex.add_re, Complex.conj_re] at k`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a0, ha0⟩` from `exists_im_ne_zero v`. Establish `h1` using `hre 1`. Establish `h2` using `hre a0`.

Rewrite `h1` using `[map_one, one_mul]`. Rewrite `h2` using `[Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero]`. Apply `Complex.ext` to reduce the goal to its premises. Conclude with `h1`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

Conclude with `absurd h ha0`. Conclude with `h`.
-/
theorem metric_disjoint_support_orthogonal (Tf : Forms0 D u) : MetricOrthogonalClasses D u := by
  intro v x y hxy
  set s := v.embedding with hs
  have hv : InfinitePlace.mk s = v := InfinitePlace.mk_embedding v
  obtain ⟨C, hC, -, -⟩ := (Tf.val 0 (Nat.zero_le _) rfl).de
  letI := D.host.cmStar
  obtain ⟨o, ho⟩ := exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s)
    (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC
  obtain ⟨Px, hPx0, hPx⟩ := polynomial_rep_of_rational_form Tf x
  obtain ⟨Py, hPy0, hPy⟩ := polynomial_rep_of_rational_form Tf y
  have hay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _) rfl).eY z) := by
    intro a c z
    rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hPy, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      map_smul, Pi.smul_apply]
  have hxay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (x + a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Px c + MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _) rfl).eY z) := by
    intro a c z
    rw [map_add, Pi.add_apply, Pi.add_apply, hPx, hay, map_add, map_add, Pi.add_apply]
  have key : ∀ a : D.what₂.LL, (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + a • y) (x + a • y)).re =
      (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re + (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (a • y) (a • y)).re := by
    intro a
    have e1 := Tf.norm 0 (Nat.zero_le _) rfl s (x + a • y) _ (hxay a) o ho
    have e2 := Tf.norm 0 (Nat.zero_le _) rfl s x Px hPx o ho
    have e3 := Tf.norm 0 (Nat.zero_le _) rfl s (a • y) _ (hay a) o ho
    rw [hv] at e1 e2 e3
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases hxy c with h | h
    · rw [hPx0 c h]
      simp only [zero_add, map_zero, norm_form_zero, Complex.zero_re, mul_zero]
    · rw [hPy0 c h]
      simp only [mul_zero, add_zero, map_zero, norm_form_zero, Complex.zero_re]
  have a1 : ∀ x x' y : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + x') y =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x' y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).1
  have a2 : ∀ x y y' : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (y + y') =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y' :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.1
  have s2 : ∀ (a : D.what₂.LL) (x y : ((D.fm u).lat 0).V), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y) =
      s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.2.2
  have hre : ∀ a : D.what₂.LL, (s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y).re = 0 := by
    intro a
    have k := key a
    rw [a1, a2, a2, majAt_swap_eq_conj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y)] at k
    rw [s2] at k
    simp only [Complex.add_re, Complex.conj_re] at k
    linarith
  obtain ⟨a0, ha0⟩ := exists_im_ne_zero v
  have h1 := hre 1
  have h2 := hre a0
  rw [map_one, one_mul] at h1
  rw [Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero] at h2
  apply Complex.ext
  · exact h1
  · rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h ha0
    · exact h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
