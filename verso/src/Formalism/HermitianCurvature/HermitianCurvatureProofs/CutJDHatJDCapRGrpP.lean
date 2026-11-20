import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsR (i : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r + i.val then j.val else j.val + 1, by have := j.isLt; have := i.isLt; split_ifs <;> omega⟩

def ginvH (g : Q.Mx k r) : Q.Mx k r := Hpk k r * gᴴ * Hpk k r

def colR (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : q.val < r then ginvH k r g *ᵥ bvec (eI k r ⟨r - 1 - q.val, by omega⟩)
  else if h2 : q.val = r then ginvH k r g *ᵥ z
  else bvec (J ⟨q.val - r - 1, by have := q.isLt; omega⟩)

def beJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => colR k r z g J q p).det

open Classical in

def jSetR : Finset (Fin (r + k) → Fin (2 * r + k + 1)) := Finset.univ.filter fun J => StrictMono J

def rhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ i : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J) •
      qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f g

end defs

def JDRRadP : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rhatOp k r z z' Y J x) c g = rhGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvP : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ => Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l`. Introduce `l`. Unfold `Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Use `fun_prop`. Establish `hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ => Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g`. Unfold `Formalism.QuantumDeterminants.Gf`. Conclude with `(Complex.continuous_normSq.comp (hD _)).sub (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))`. Unfold `OmP`.

Rewrite using `[Set.setOf_and, Set.setOf_forall]`. Conclude with `(isOpen_lt continuous_const hG).inter (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)`. Introduce and unpack `g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩`. Establish `hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z` using `⟨h, hh, m, hm.1, rfl⟩`. Establish `hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z'` using `⟨h', hh', m', hm'.1, rfl⟩`.

Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']`. Conclude with `hgD.1`. Rewrite using `[Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']`. Conclude with `hgD.2 a`.
-/
private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

/- English proof (translation)
Establish `hl` using `l.isLt`. Establish `hes : eI k r l ≠ esI k r l`. Simplify using `only [eI, esI, ne_eq, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hcol : ∀ j q, Q.w1 k r l x j q = if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0`.

Introduce `j q`. Simplify using `only [Q.w1]`. Apply the tactic sequence `by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>`. Apply the tactic sequence `by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>`. Apply the tactic sequence `(intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)`.

Establish `hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0`. Introduce `p hp`. Rewrite `hp` using `[Ne, Fin.ext_iff]`. Simplify using `only [esI] at hp`. Simplify using `only [Hpk, eI, Fin.ext_iff]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0`. Introduce `p hp`. Rewrite `hp` using `[Ne, Fin.ext_iff]`. Simplify using `only [eI] at hp`.

Simplify using `only [Hpk, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0`. Introduce `q hq`. Rewrite `hq` using `[Ne, Fin.ext_iff]`.

Simplify using `only [esI] at hq`. Simplify using `only [Hpk, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0`. Introduce `q hq`.

Rewrite `hq` using `[Ne, Fin.ext_iff]`. Simplify using `only [eI] at hq`. Simplify using `only [Hpk, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `hHes : Hpk k r (eI k r l) (esI k r l) = 1`.

Establish `h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k` using `by omega`. Simplify using `[Hpk, eI, esI, hl, h1]`. Establish `hHse : Hpk k r (esI k r l) (eI k r l) = 1`. Establish `h2 : ¬ (2 * r + k - (l : ℕ) < r)` using `by omega`. Establish `h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k` using `by omega`.

Simplify using `[Hpk, eI, esI, hl, h2, h3]`. Use `show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r`. Use extensionality with `p q`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Apply the tactic sequence `by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>`.

Apply the tactic sequence `by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>`. Use `first`. Consider the case `exact absurd (hp1.symm.trans hp2) hes`. Consider the case `exact absurd (hq1.symm.trans hq2) hes`. Consider the case `simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]`.
-/
private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

/- English proof (translation)
Establish `hg' : gᴴ * H * g = H` using `hg`. Establish `hh' : hᴴ * H * h = H` using `hh`. Use `show (g * h)ᴴ * H * (g * h) = H`. Rewrite using `[Matrix.conjTranspose_mul, show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']`.
-/
private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

/- English proof (translation)
Unfold `Q.wCell`. Proceed by induction on `((List.finRange r).filter fun a => a.val < i.val) with`. Consider the case `nil => show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules. Consider the case `cons a L ih`.

Rewrite using `[List.map_cons, List.prod_cons]`. Conclude with `mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih`.
-/
private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩`.
-/
private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

/- English proof (translation)
Introduce `Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y`. Take `⟨ε, hε⟩` from `hR S.G.k S.G.r`. Take `⟨Θ, hP, hC, hA⟩` from `hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y`. Use `⟨Θ, hP, hC, ?_⟩` and prove the remaining obligations. Introduce `J hJ c hc g hg hx`.

Establish `key` using `hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx`. Rewrite using `[← key]`. Establish `hx0` using `wCell_last_mul_mem_Glev_zero c hc g hg`. Take `⟨U, F, hU, hxU, hF, hFJ⟩` from `hJ.1 _ ⟨hx0, hx⟩`. Establish `hS : Q.SmoothLev S.G.k S.G.r 0 U J` using `fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩`.

Use `hA U J hU hS _ ⟨hx0, hxU⟩` as an intermediate fact. Simplify using `only [Q.resG, this]`.
-/
theorem jDRGrpP_of_parts (hR : JDRRadP) (hI : JDRRealInvP) : JDRGrpP := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
