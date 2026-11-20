import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.SmallPI

noncomputable section

open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl.StarPf

section

variable {A V : Type} [Ring A] [Algebra ℂ A]

def restrictAlg [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) : A →ₐ[ℂ] Module.End ℂ W where
  toFun h := (ρ h).restrict (hW h)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem restrictAlg_coe [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (h : A) (x : W) : ((restrictAlg ρ W hW h x : W) : V) = ρ h x := rfl

/- English proof (translation)
Introduce `h x hx`. Take `⟨hxU, hxW⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨?_, hW h x hxW⟩` and prove the remaining obligations. Rewrite `hxU`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Take `⟨h', hh'⟩` from `hs h`. Rewrite using `[← inner_conj_symm, hh' x u, inner_conj_symm]`. Conclude with `hxU _ (hU h' u hu)`.
-/
theorem inf_orthogonal_invariant [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hs : StarClosed ρ) {U W : Submodule ℂ V}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∀ h, ∀ x ∈ Uᗮ ⊓ W, ρ h x ∈ Uᗮ ⊓ W := by
  intro h x hx
  obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨?_, hW h x hxW⟩
  rw [Submodule.mem_orthogonal] at hxU ⊢
  intro u hu
  obtain ⟨h', hh'⟩ := hs h
  rw [← inner_conj_symm, hh' x u, inner_conj_symm]
  exact hxU _ (hU h' u hu)

end

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => show f 1 = 1`. Conclude with `map_one f`. Consider the case `cons a l ih => show f (1 * a * word 1 l) = 1 * f a * word 1 (l.map f)`. Rewrite using `[map_mul, map_mul, map_one, ih]`.
-/
private theorem map_word_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (l : List A) : f (word 1 l) = word 1 (l.map f) := by
  induction l with
  | nil =>
    show f 1 = 1
    exact map_one f
  | cons a l ih =>
    show f (1 * a * word 1 l) = 1 * f a * word 1 (l.map f)
    rw [map_mul, map_mul, map_one, ih]

/- English proof (translation)
Unfold `stdPoly`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_word_one, List.map_ofFn]`. Both sides reduce to the same expression.
-/
private theorem map_stdPoly_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) {M : ℕ} (b : Fin M → A) : f (stdPoly 1 b) = stdPoly 1 (fun i => f (b i)) := by
  unfold stdPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_mul, map_intCast, map_word_one, List.map_ofFn]
  rfl

/- English proof (translation)
Unfold `StStar`. Introduce `C A _ _ hirr`. It suffices to establish `key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V], Module.finrank ℂ V = n → ∀ (ρ : A →ₐ[ℂ] Module.End ℂ V), StarClosed ρ → ∀ (b : Fin (C ^ 2 + 1) → A), ρ (stdPoly 1 b) = 0 by`. Introduce `V _ _ _ ρ hs b`. Conclude with `key _ V rfl ρ hs b`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ hn ρ hs b`. Break down `Nat.eq_zero_or_pos n with hn0 | hnpos` into its components or cases.

Establish `: Subsingleton V` using `Module.finrank_zero_iff.mp (hn.trans hn0)`. Conclude with `LinearMap.ext fun v => Subsingleton.elim _ _`. Establish `: Nontrivial V` using `Module.finrank_pos_iff.mp (hn ▸ hnpos)`. Establish `hex : ∃ d, ∃ W : Submodule ℂ V, ((∀ h, ∀ w ∈ W, ρ h w ∈ W) ∧ W ≠ ⊥) ∧ Module.finrank ℂ W = d` using `⟨_, ⊤, ⟨fun _ _ _ => Submodule.mem_top, bot_ne_top.symm⟩, rfl⟩`. Take `⟨W, ⟨hWinv, hWne⟩, hWd⟩` from `Nat.find_spec hex`.

Establish `hmin : ∀ W' : Submodule ℂ V, (∀ h, ∀ w ∈ W', ρ h w ∈ W') → W' ≠ ⊥ → Module.finrank ℂ W ≤ Module.finrank ℂ W'`. Introduce `W' h1 h2`. Rewrite using `[hWd]`. Conclude with `Nat.find_min' hex ⟨W', ⟨h1, h2⟩, rfl⟩`. Establish `hWirr : ∀ U : Submodule ℂ W, (∀ h, ∀ u ∈ U, restrictAlg ρ W hWinv h u ∈ U) → U = ⊥ ∨ U = ⊤`.

Introduce `U hU`. Distinguish the cases in `hUb : U = ⊥`. Conclude with `Or.inl hUb`. Use `right`. Establish `hU'inv : ∀ h, ∀ v ∈ U.map W.subtype, ρ h v ∈ U.map W.subtype`.

Introduce `h v hv`. Take `⟨u, hu, rfl⟩` from `Submodule.mem_map.mp hv`. Conclude with `Submodule.mem_map.mpr ⟨restrictAlg ρ W hWinv h u, hU h u hu, restrictAlg_coe ρ W hWinv h u⟩`. Establish `hfr : Module.finrank ℂ (U.map W.subtype) = Module.finrank ℂ U` using `Submodule.finrank_map_subtype_eq W U`. Establish `hU'ne : U.map W.subtype ≠ ⊥`.

Introduce `h0`. Apply `hUb` to reduce the goal to its premises. Apply `Submodule.finrank_eq_zero.mp` to reduce the goal to its premises. Rewrite using `[← hfr]`. Conclude with `Submodule.finrank_eq_zero.mpr h0`.

Establish `h1` using `hmin _ hU'inv hU'ne`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Conclude with `le_antisymm (Submodule.finrank_le U) (hfr ▸ h1)`. Establish `hdimW : Module.finrank ℂ W ≤ C` using `hirr W (restrictAlg ρ W hWinv) hWirr`. Establish `hlt : Module.finrank ℂ W ^ 2 < C ^ 2 + 1` using `Nat.lt_succ_of_le (Nat.pow_le_pow_left hdimW 2)`.

Establish `hPW : ∀ w ∈ W, ρ (stdPoly 1 b) w = 0`. Introduce `w hw`. Rewrite using `[map_stdPoly_one ρ b]`. Conclude with `CompanionTheory.D.gk.admitted.small_irreducible_representation V W W le_rfl 1 (fun w hw => hw) (C ^ 2 + 1) hlt (fun i => ρ (b i)) (fun i w hw => hWinv (b i) w hw) w hw`. Establish `hperp : ∀ h, ∀ x ∈ Wᗮ, ρ h x ∈ Wᗮ`.

Introduce `h x hx`. Establish `h1` using `inf_orthogonal_invariant ρ hs (U := W) (W := ⊤) hWinv (fun _ _ _ => Submodule.mem_top) h x (Submodule.mem_inf.mpr ⟨hx, Submodule.mem_top⟩)`. Conclude with `(Submodule.mem_inf.mp h1).1`. Establish `hs2 : StarClosed (restrictAlg ρ Wᗮ hperp)`. Introduce `h`.

Take `⟨h', hh'⟩` from `hs h`. Use `⟨h', fun u w => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, restrictAlg_coe, restrictAlg_coe]`. Conclude with `hh' u w`. Establish `hWpos : 0 < Module.finrank ℂ W` using `Nat.pos_of_ne_zero fun h0 => hWne (Submodule.finrank_eq_zero.mp h0)`.

Establish `hsum` using `Submodule.finrank_add_finrank_orthogonal W`. Establish `hltp : Module.finrank ℂ Wᗮ < n` using `by omega`. Establish `hrest` using `ih _ hltp Wᗮ rfl (restrictAlg ρ Wᗮ hperp) hs2 b`. Establish `hPperp : ∀ x ∈ Wᗮ, ρ (stdPoly 1 b) x = 0`. Introduce `x hx`.

Establish `h0` using `congrArg (fun T => ((T ⟨x, hx⟩ : Wᗮ) : V)) hrest`. Simplify `h0` using `[restrictAlg_coe]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ W ⊔ Wᗮ`. Establish `htop : W ⊔ Wᗮ = ⊤`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq W Wᗮ`. Establish `h2 : W ⊓ Wᗮ = ⊥` using `disjoint_iff.mp (Submodule.orthogonal_disjoint W)`. Rewrite `h1` using `[h2, Submodule.finrank_eq_zero.mpr rfl]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Take `⟨w, hw, x, hx, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[map_add, hPW w hw, hPperp x hx, add_zero, LinearMap.zero_apply]`.
-/
theorem stStar : StStar := by
  unfold StStar
  intro C A _ _ hirr
  suffices key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = n → ∀ (ρ : A →ₐ[ℂ] Module.End ℂ V), StarClosed ρ →
        ∀ (b : Fin (C ^ 2 + 1) → A), ρ (stdPoly 1 b) = 0 by
    intro V _ _ _ ρ hs b
    exact key _ V rfl ρ hs b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn ρ hs b
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
  have hex : ∃ d, ∃ W : Submodule ℂ V, ((∀ h, ∀ w ∈ W, ρ h w ∈ W) ∧ W ≠ ⊥) ∧ Module.finrank ℂ W = d :=
    ⟨_, ⊤, ⟨fun _ _ _ => Submodule.mem_top, bot_ne_top.symm⟩, rfl⟩
  obtain ⟨W, ⟨hWinv, hWne⟩, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, (∀ h, ∀ w ∈ W', ρ h w ∈ W') → W' ≠ ⊥ →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWd]
    exact Nat.find_min' hex ⟨W', ⟨h1, h2⟩, rfl⟩
  have hWirr : ∀ U : Submodule ℂ W, (∀ h, ∀ u ∈ U, restrictAlg ρ W hWinv h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    right
    have hU'inv : ∀ h, ∀ v ∈ U.map W.subtype, ρ h v ∈ U.map W.subtype := by
      intro h v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      exact Submodule.mem_map.mpr ⟨restrictAlg ρ W hWinv h u, hU h u hu, restrictAlg_coe ρ W hWinv h u⟩
    have hfr : Module.finrank ℂ (U.map W.subtype) = Module.finrank ℂ U := Submodule.finrank_map_subtype_eq W U
    have hU'ne : U.map W.subtype ≠ ⊥ := by
      intro h0
      apply hUb
      apply Submodule.finrank_eq_zero.mp
      rw [← hfr]
      exact Submodule.finrank_eq_zero.mpr h0
    have h1 := hmin _ hU'inv hU'ne
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le U) (hfr ▸ h1)
  have hdimW : Module.finrank ℂ W ≤ C := hirr W (restrictAlg ρ W hWinv) hWirr
  have hlt : Module.finrank ℂ W ^ 2 < C ^ 2 + 1 := Nat.lt_succ_of_le (Nat.pow_le_pow_left hdimW 2)
  have hPW : ∀ w ∈ W, ρ (stdPoly 1 b) w = 0 := by
    intro w hw
    rw [map_stdPoly_one ρ b]
    exact CompanionTheory.D.gk.admitted.small_irreducible_representation V W W le_rfl 1 (fun w hw => hw) (C ^ 2 + 1) hlt (fun i => ρ (b i))
      (fun i w hw => hWinv (b i) w hw) w hw
  have hperp : ∀ h, ∀ x ∈ Wᗮ, ρ h x ∈ Wᗮ := by
    intro h x hx
    have h1 := inf_orthogonal_invariant ρ hs (U := W) (W := ⊤) hWinv (fun _ _ _ => Submodule.mem_top) h x
      (Submodule.mem_inf.mpr ⟨hx, Submodule.mem_top⟩)
    exact (Submodule.mem_inf.mp h1).1
  have hs2 : StarClosed (restrictAlg ρ Wᗮ hperp) := by
    intro h
    obtain ⟨h', hh'⟩ := hs h
    refine ⟨h', fun u w => ?_⟩
    rw [Submodule.coe_inner, Submodule.coe_inner, restrictAlg_coe, restrictAlg_coe]
    exact hh' u w
  have hWpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero fun h0 => hWne (Submodule.finrank_eq_zero.mp h0)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hltp : Module.finrank ℂ Wᗮ < n := by omega
  have hrest := ih _ hltp Wᗮ rfl (restrictAlg ρ Wᗮ hperp) hs2 b
  have hPperp : ∀ x ∈ Wᗮ, ρ (stdPoly 1 b) x = 0 := by
    intro x hx
    have h0 := congrArg (fun T => ((T ⟨x, hx⟩ : Wᗮ) : V)) hrest
    simpa [restrictAlg_coe] using h0
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ W ⊔ Wᗮ := by
    have htop : W ⊔ Wᗮ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Wᗮ
      have h2 : W ⊓ Wᗮ = ⊥ := disjoint_iff.mp (Submodule.orthogonal_disjoint W)
      rw [h2, Submodule.finrank_eq_zero.mpr rfl] at h1
      omega
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hPW w hw, hPperp x hx, add_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.RgFl.StarPf
