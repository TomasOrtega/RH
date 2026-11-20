import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibniz
import Development.EtaleCohomology.KummerTheory.CupAWCutEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

/- English proof (translation)
Consider the cases of `p with`. Consider the case `zero => simp [bd]`. Consider the case `succ p => simp [bd, map_sum, map_zsmul]`.
-/
theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

/- English proof (translation)
Consider the cases of `p with`. Consider the case `zero => rw [ev_delta_zero hm α s t hs ht U x]`. Simplify using `[bd]`. Consider the case `succ p`. Rewrite using `[ev_delta_succ hm α p s t hs ht U x]`.

Use `congr 2`. Simplify using `only [bd]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by omega)]`.
-/
theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev α q t hh U z else 0) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs ht U x]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs ht U x]
    congr 2
    simp only [bd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos (by omega)]

/- English proof (translation)
Substitute `hs ht hs' ht'` using the available equality. Both sides reduce to the same expression.
-/
theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = μ.mul U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

/- English proof (translation)
Substitute `hs ht hw` using the available equality. Conclude with `μ.leibniz U s t w h a b`.
-/
theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

/- English proof (translation)
The claim follows from `bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y`.
-/
theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

/- English proof (translation)
The claim follows from `bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y`.
-/
theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

/- English proof (translation)
The claim follows from `map_sum ((φ.hom.app (op U)).hom) f s`.
-/
theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

/- English proof (translation)
The claim follows from `map_zsmul ((φ.hom.app (op U)).hom) c a`.
-/
theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

/- English proof (translation)
Substitute `hF hB` using the available equality. Simplify using `only [smul_add, smul_smul]`. Rewrite using `[h2, h3, h4]`. Normalize the expressions using the abelian group laws.
-/
theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

/- English proof (translation)
Simplify using `[Int.negOnePow_def]`.
-/
theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib

open LateralTheory.EtaleFoundations.AWLeib in

/- English proof (translation)
Introduce `R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2`. Apply `ev_ext` to reduce the goal to its premises. Introduce `N w hw U x`. Rewrite using `[ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x, h2 N w hw U x]`. Rewrite using `[bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) • Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]`.

Use `swap`. Introduce `N' y hN`. Rewrite using `[dif_pos (by omega), hγ N' w _ U y]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`.

Unfold `Fm`. Rewrite using `[dif_pos (by omega)]`. Rewrite using `[bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ)) (fun p => by congr 2; push_cast; ring) N x]`. Rewrite using `[secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Establish `hp` using `p.2`. Rewrite using `[Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]`. Rewrite using `[ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]`. Simplify using `only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]`. Use `recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Use `bd_congr (fun q z hq => ?_) _` and prove the remaining obligations. Rewrite using `[dif_pos (by omega)]`. Unfold `Fm`. Rewrite using `[dif_pos (by omega)]`. Conclude with `mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`.

Use `bd_congr (fun q z hq => ?_) _` and prove the remaining obligations. Rewrite using `[dif_pos (by omega)]`. Unfold `Fm`. Rewrite using `[dif_pos (by omega)]`. Conclude with `mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`.

Simplify using `only [← Units.val_mul, ← Int.negOnePow_add]`. Use `congr 1`. Rewrite using `[Int.negOnePow_eq_iff]`. Conclude with `⟨-((p : ℕ) : ℤ), by ring⟩`. Substitute `hk` using the available equality.

Simplify using `only [← Units.val_mul, ← Int.negOnePow_add]`. Use `congr 1`. Rewrite using `[Int.negOnePow_eq_iff]`. Conclude with `⟨0, by ring⟩`. Substitute `hk` using the available equality.

Rewrite using `[sign_nat]`. Simplify using `only [← Units.val_mul, ← Int.negOnePow_add]`. Use `congr 1`. Rewrite using `[Int.negOnePow_eq_iff]`. Conclude with `⟨0, by ring⟩`.
-/
theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2
  apply ev_ext
  intro N w hw U x
  rw [ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x,
    h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dif_pos (by omega), hγ N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fm
    rw [dif_pos (by omega)]
  rw [bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]
  rw [ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]
  refine recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    rw [dif_pos (by omega)]
    unfold Fm
    rw [dif_pos (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    rw [dif_pos (by omega)]
    unfold Fm
    rw [dif_pos (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-((p : ℕ) : ℤ), by ring⟩
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
