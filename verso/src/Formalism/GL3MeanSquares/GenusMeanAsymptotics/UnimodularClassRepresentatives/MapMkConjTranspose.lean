import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardMapEquiv
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

def isoCount (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) : ℕ :=
  Nat.card {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    Xᴴ * g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`. Both sides reduce to the same expression.
-/
theorem map_mk_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) :
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = gᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rfl

/- English proof (translation)
Establish `h2 : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤` using `Ideal.sup_pow_eq_top hδ`. Rewrite `h2` using `[Ideal.eq_top_iff_one, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, hyz⟩` from `h2`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `hq : Ideal.Quotient.mk (extP K 𝔭 ^ N) (δ * a) = Ideal.Quotient.mk (extP K 𝔭 ^ N) 1`.

Rewrite using `[Ideal.Quotient.eq]`. Establish `hza : δ * a - 1 = -z`. Rewrite using `[← hyz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hza]`.

Conclude with `neg_mem hz`. Rewrite `hq` using `[map_mul, map_one]`. Conclude with `isUnit_iff_exists_inv.mpr ⟨_, hq⟩`.
-/
theorem isUnit_mk {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) δ) := by
  have h2 : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := Ideal.sup_pow_eq_top hδ
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := h2
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hq : Ideal.Quotient.mk (extP K 𝔭 ^ N) (δ * a) = Ideal.Quotient.mk (extP K 𝔭 ^ N) 1 := by
    rw [Ideal.Quotient.eq]
    have hza : δ * a - 1 = -z := by
      rw [← hyz]
      ring
    rw [hza]
    exact neg_mem hz
  rw [map_mul, map_one] at hq
  exact isUnit_iff_exists_inv.mpr ⟨_, hq⟩

/- English proof (translation)
Establish `hF` using `hFF.out`. Use `finite_quot (K := K) h𝔭 (k + 1)` as an intermediate fact. Take `⟨θ, hθ⟩` from `exists_theta hK hF h𝔭`. Take `⟨e, he⟩` from `exists_inv_theta hθ (k + 1)`. Establish `he' : (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ - star (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ)) * Ideal.Quotient.mk _ e = 1`.

Rewrite using `[star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))]`. Conclude with `Ideal.Quotient.eq.2 he`. Establish `h` using `FirstPropositionFrame.card_lift_unimod' (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k) (by`. Introduce `a ha b hb`. Rewrite `ha`, `hb` using `[ker_piQ]`.

Conclude with `mul_eq_zero_idQ (by omega) ha hb) he'`. Use the proof step `(g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1))))`. Use the proof step `(by rw [map_mk_conjTranspose, hg])`. Use the proof step `(by`. Establish `: (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).det = Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) g.det` using `(RingHom.map_det _ g).symm`.

Rewrite using `[this]`. Conclude with `isUnit_mk hdet _)`. Use the proof step `(Ideal.absNorm 𝔭) (card_ker_piQ hK hF h𝔭 k)`. Rewrite `h` using `[Fintype.card_fin]`. Establish `hm : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).map (piQ K 𝔭 k) = g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite `h` using `[hm]`. Conclude with `h`.
-/
theorem isoCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) {k : ℕ} (hk : 1 ≤ k) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (m ^ 2) * isoCount 𝔭 k g := by
  have hF := hFF.out
  have := finite_quot (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ (k + 1)
  have he' : (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ -
      star (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ)) * Ideal.Quotient.mk _ e = 1 := by
    rw [star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))]
    exact Ideal.Quotient.eq.2 he
  have h := FirstPropositionFrame.card_lift_unimod' (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k)
    (by
      intro a ha b hb
      rw [ker_piQ] at ha hb
      exact mul_eq_zero_idQ (by omega) ha hb) he'
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1))))
    (by rw [map_mk_conjTranspose, hg])
    (by
      have : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).det =
          Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) g.det := (RingHom.map_det _ g).symm
      rw [this]
      exact isUnit_mk hdet _)
    (Ideal.absNorm 𝔭) (card_ker_piQ hK hF h𝔭 k)
  rw [Fintype.card_fin] at h
  have hm : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).map (piQ K 𝔭 k) =
      g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    ext i j
    rfl
  rw [hm] at h
  exact h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[isoCount_succ hK h𝔭 g hg hdet (by omega), ih, ← mul_assoc, ← pow_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isoCount_eq_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (k * m ^ 2) * isoCount 𝔭 1 g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [isoCount_succ hK h𝔭 g hg hdet (by omega), ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
