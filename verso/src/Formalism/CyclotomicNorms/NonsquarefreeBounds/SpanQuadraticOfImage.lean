import Formalism.CyclotomicNorms.StatementA

noncomputable section

open Module

namespace Formalism.CyclotomicNorms

namespace PrismSpan

/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules.
-/
theorem sum_single {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] (v : ∀ i, X i) : ∑ i, Pi.single i (v i) = v := by
  ext; simp

variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

def diag (ρ : ∀ i, Representation k G (W i)) : G →* (∀ i, Module.End k (W i)) where
  toFun g i := ρ i g
  map_one' := by funext i; exact map_one (ρ i)
  map_mul' g h := by funext i; exact map_mul (ρ i) g h

abbrev alg (ρ : ∀ i, Representation k G (W i)) : Subalgebra k (∀ i, Module.End k (W i)) :=
  (MonoidAlgebra.lift k (∀ i, Module.End k (W i)) G (diag ρ)).range

variable (ρ : ∀ i, Representation k G (W i))

/- English proof (translation)
Assemble the required witnesses or components as `⟨MonoidAlgebra.single g 1, by simp⟩`.
-/
theorem diag_mem (g : G) : diag ρ g ∈ alg ρ :=
  ⟨MonoidAlgebra.single g 1, by simp⟩

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `show E j (Pi.single i w j) = _`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hj]`.
-/
theorem pi_smul_single (E : ∀ j, Module.End k (W j)) (i : Fin a) (w : W i) :
    E • (Pi.single i w : ∀ j, W j) = Pi.single i (E i w) := by
  funext j
  show E j (Pi.single i w j) = _
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show ((algebraMap k (alg ρ) c : ∀ i, Module.End k (W i))) i (m i) = c • m i`. Simplify using the standard rewrite rules.
-/
theorem alg_smul_eq (c : k) (m : ∀ i, W i) : (algebraMap k (alg ρ) c) • m = c • m := by
  funext i
  show ((algebraMap k (alg ρ) c : ∀ i, Module.End k (W i))) i (m i) = c • m i
  simp

variable {ρ}

/- English proof (translation)
Establish `hX : X ∈ Submodule.span k (Set.range (ρ i))` using `by rw [hspan i]; trivial`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨g, rfl⟩ := hx`. Conclude with `⟨diag ρ g, diag_mem ρ g, rfl⟩`. Consider the case `zero => exact ⟨0, Subalgebra.zero_mem _, rfl⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨s, hs, rfl⟩` from `hy`. Conclude with `⟨r + s, add_mem hr hs, rfl⟩`. Consider the case `smul c x _ hx`.

Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨c • r, Subalgebra.smul_mem _ hr c, rfl⟩`.
-/
theorem proj_surj (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a)
    (X : Module.End k (W i)) : ∃ r ∈ alg ρ, r i = X := by
  have hX : X ∈ Submodule.span k (Set.range (ρ i)) := by rw [hspan i]; trivial
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ⟨diag ρ g, diag_mem ρ g, rfl⟩
  | zero => exact ⟨0, Subalgebra.zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, add_mem hr hs, rfl⟩
  | smul c x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨c • r, Subalgebra.smul_mem _ hr c, rfl⟩

/- English proof (translation)
Take `⟨μ, hμ⟩` from `Module.Projective.exists_dual_ne_zero k hv`. Conclude with `⟨(μ v)⁻¹ • μ.smulRight w, by simp [smul_smul, inv_mul_cancel₀ hμ]⟩`.
-/
theorem exists_end {V : Type} [AddCommGroup V] [Module k V] {v : V} (hv : v ≠ 0) (w : V) :
    ∃ X : Module.End k V, X v = w := by
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero k hv
  exact ⟨(μ v)⁻¹ • μ.smulRight w, by simp [smul_smul, inv_mul_cancel₀ hμ]⟩

variable (ρ) in

def coordSub (i : Fin a) : Submodule (alg ρ) (∀ j, W j) where
  carrier := {v | ∀ j, j ≠ i → v j = 0}
  add_mem' {u v} hu hv j hj := by
    show u j + v j = 0
    rw [hu j hj, hv j hj, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r v hv j hj := by
    show (r : ∀ i, Module.End k (W i)) j (v j) = 0
    rw [hv j hj, map_zero]

/- English proof (translation)
Introduce `_ hj` and use `Pi.single_eq_of_ne hj w`.
-/
theorem single_mem (i : Fin a) (w : W i) : (Pi.single i w : ∀ j, W j) ∈ coordSub ρ i :=
  fun _ hj => Pi.single_eq_of_ne hj w

/- English proof (translation)
Rewrite using `[isSimpleModule_iff_isAtom]`. Use `⟨?_, fun N hN => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `exists_ne (0 : W i)`. Introduce `h`. Establish `h1 : (Pi.single i w : ∀ j, W j) ∈ (⊥ : Submodule (alg ρ) (∀ j, W j))` using `h ▸ single_mem i w`.

Rewrite `h1` using `[Submodule.mem_bot]`. Conclude with `hw (by simpa using congrFun h1 i)`. Assume the negation of the conclusion as `hN0`. Take `⟨v, hvN, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hN0`. Establish `hvi : v i ≠ 0`.

Introduce `h`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Conclude with `h`. Conclude with `hN.le hvN j hj`. Use `hN.ne (le_antisymm hN.le fun u hu => ?_)` and prove the remaining obligations. Take `⟨X, hX⟩` from `exists_end (k := k) hvi (u i)`. Take `⟨r, hr, rfl⟩` from `proj_surj hspan i X`.

Establish `h2 : (⟨r, hr⟩ : alg ρ) • v = u`. Use function extensionality and compare the values at `j`. Use `show r j (v j) = u j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Conclude with `hX`. Rewrite using `[hN.le hvN j hj, hu j hj, map_zero]`. Conclude with `h2 ▸ N.smul_mem _ hvN`.
-/
theorem coord_simple (hnt : ∀ i, Nontrivial (W i))
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) (i : Fin a) :
    IsSimpleModule (alg ρ) (coordSub ρ i) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun N hN => ?_⟩
  · obtain ⟨w, hw⟩ := exists_ne (0 : W i)
    intro h
    have h1 : (Pi.single i w : ∀ j, W j) ∈ (⊥ : Submodule (alg ρ) (∀ j, W j)) :=
      h ▸ single_mem i w
    rw [Submodule.mem_bot] at h1
    exact hw (by simpa using congrFun h1 i)
  · by_contra hN0
    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    have hvi : v i ≠ 0 := by
      intro h
      apply hv0
      funext j
      by_cases hj : j = i
      · subst hj; exact h
      · exact hN.le hvN j hj
    refine hN.ne (le_antisymm hN.le fun u hu => ?_)
    obtain ⟨X, hX⟩ := exists_end (k := k) hvi (u i)
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    have h2 : (⟨r, hr⟩ : alg ρ) • v = u := by
      funext j
      show r j (v j) = u j
      by_cases hj : j = i
      · subst hj; exact hX
      · rw [hN.le hvN j hj, hu j hj, map_zero]
    exact h2 ▸ N.smul_mem _ hvN

/- English proof (translation)
Apply `IsSemisimpleModule.of_sSup_simples_eq_top` to reduce the goal to its premises. Use `eq_top_iff.mpr fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_single v]`. Conclude with `Submodule.sum_mem _ fun i _ => (le_sSup (show coordSub ρ i ∈ {m : Submodule (alg ρ) (∀ j, W j) | IsSimpleModule _ m} from coord_simple hnt hspan i) : coordSub ρ i ≤ _) (single_mem i (v i))`.
-/
theorem semisimple (hnt : ∀ i, Nontrivial (W i))
    (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤) :
    IsSemisimpleModule (alg ρ) (∀ j, W j) := by
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  refine eq_top_iff.mpr fun v _ => ?_
  rw [← sum_single v]
  exact Submodule.sum_mem _ fun i _ =>
    (le_sSup (show coordSub ρ i ∈ {m : Submodule (alg ρ) (∀ j, W j) | IsSimpleModule _ m} from
      coord_simple hnt hspan i) : coordSub ρ i ≤ _) (single_mem i (v i))

/- English proof (translation)
Set `ψ : W i →ₗ[k] W j` to `{ toFun := fun w => φ (Pi.single i w) j map_add' := fun x y => by show φ (Pi.single i (x + y)) j = φ (Pi.single i x) j + φ (Pi.single i y) j`. Rewrite using `[Pi.single_add, map_add]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c x => by show φ (Pi.single i (c • x)) j = c • φ (Pi.single i x) j`. Rewrite using `[Pi.single_smul, ← alg_smul_eq ρ c, φ.map_smul, alg_smul_eq]`.

Use `rfl }`. Establish `hint : ∀ r ∈ alg ρ, ∀ x, ψ (r i x) = r j (ψ x)`. Introduce `r hr x`. Use `show φ (Pi.single i (r i x)) j = r j (φ (Pi.single i x) j)`. Rewrite using `[← pi_smul_single r i x]`.

Conclude with `congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i x)) j`. Assume the negation of the conclusion as `hw`. Establish `hinj : Function.Injective ψ`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `u hu`.

Assume the negation of the conclusion as `hu0`. Take `⟨X, hX⟩` from `exists_end (k := k) hu0 w`. Take `⟨r, hr, rfl⟩` from `proj_surj hspan i X`. Apply `hw` to reduce the goal to its premises. Use `show ψ w = 0`.

Rewrite using `[← hX, hint r hr, LinearMap.mem_ker.mp hu, map_zero]`. Establish `hsurj : Function.Surjective ψ`. Introduce `y`. Take `⟨Y, hY⟩` from `exists_end (k := k) (show ψ w ≠ 0 from hw) y`. Take `⟨r, hr, rfl⟩` from `proj_surj hspan j Y`.

Conclude with `⟨r i w, by rw [hint r hr, hY]⟩`. Conclude with `hne i j hij ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun g x => hint _ (diag_mem ρ g) x⟩`.
-/
theorem off_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) {i j : Fin a} (hij : i ≠ j) (w : W i) :
    φ (Pi.single i w) j = 0 := by
  let ψ : W i →ₗ[k] W j :=
    { toFun := fun w => φ (Pi.single i w) j
      map_add' := fun x y => by
        show φ (Pi.single i (x + y)) j = φ (Pi.single i x) j + φ (Pi.single i y) j
        rw [Pi.single_add, map_add]; rfl
      map_smul' := fun c x => by
        show φ (Pi.single i (c • x)) j = c • φ (Pi.single i x) j
        rw [Pi.single_smul, ← alg_smul_eq ρ c, φ.map_smul, alg_smul_eq]; rfl }
  have hint : ∀ r ∈ alg ρ, ∀ x, ψ (r i x) = r j (ψ x) := by
    intro r hr x
    show φ (Pi.single i (r i x)) j = r j (φ (Pi.single i x) j)
    rw [← pi_smul_single r i x]
    exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i x)) j
  by_contra hw
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    by_contra hu0
    obtain ⟨X, hX⟩ := exists_end (k := k) hu0 w
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    apply hw
    show ψ w = 0
    rw [← hX, hint r hr, LinearMap.mem_ker.mp hu, map_zero]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨Y, hY⟩ := exists_end (k := k) (show ψ w ≠ 0 from hw) y
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan j Y
    exact ⟨r i w, by rw [hint r hr, hY]⟩
  exact hne i j hij ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩,
    fun g x => hint _ (diag_mem ρ g) x⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `proj_surj hspan i X`. Rewrite using `[← pi_smul_single r i w]`. Conclude with `congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i w)) i`.
-/
theorem on_diag (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (i : Fin a) (X : Module.End k (W i)) (w : W i) :
    φ (Pi.single i (X w)) i = X (φ (Pi.single i w) i) := by
  obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
  rw [← pi_smul_single r i w]
  exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i w)) i

/- English proof (translation)
Establish `key : ∀ i (w : W i), φ (Pi.single i (E i w)) = E • φ (Pi.single i w)`. Introduce `i w`. Use function extensionality and compare the values at `j`. Use `show _ = E j (φ (Pi.single i w) j)`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Conclude with `on_diag hspan φ i (E i) w`. Rewrite using `[off_diag hspan hne φ hij, off_diag hspan hne φ hij, map_zero]`. Use `conv_lhs => rw [← sum_single m]`. Use `conv_rhs => rw [← sum_single m]`.

Simplify using `only [Finset.smul_sum, map_sum, pi_smul_single, key]`.
-/
theorem comm (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) (E : ∀ j, Module.End k (W j)) (m : ∀ j, W j) :
    φ (E • m) = E • φ m := by
  have key : ∀ i (w : W i), φ (Pi.single i (E i w)) = E • φ (Pi.single i w) := by
    intro i w
    funext j
    show _ = E j (φ (Pi.single i w) j)
    by_cases hij : i = j
    · subst hij; exact on_diag hspan φ i (E i) w
    · rw [off_diag hspan hne φ hij, off_diag hspan hne φ hij, map_zero]
  conv_lhs => rw [← sum_single m]
  conv_rhs => rw [← sum_single m]
  simp only [Finset.smul_sum, map_sum, pi_smul_single, key]

end PrismSpan

namespace PrismSpan

variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  {La : Fin a → Type} [∀ i, AddCommGroup (La i)] [∀ i, Module k (La i)]

def post (x : ∀ i, La i →ₗ[k] W i) :
    (∀ i, Module.End k (W i)) →ₗ[k] (∀ i, La i →ₗ[k] W i) where
  toFun E i := E i ∘ₗ x i
  map_add' E F := by funext i; exact LinearMap.add_comp _ _ _
  map_smul' c E := by funext i; exact LinearMap.smul_comp _ _ _

def sr (i : Fin a) (w : W i) : Module.Dual k (La i) →ₗ[k] (∀ j, La j →ₗ[k] W j) where
  toFun ψ := Pi.single i (ψ.smulRight w)
  map_add' ψ ψ' := by
    rw [← Pi.single_add]; congr 1; ext; simp [add_smul]
  map_smul' c ψ := by
    rw [RingHom.id_apply, ← Pi.single_smul]; congr 1; ext; simp [smul_smul]

end PrismSpan

end Formalism.CyclotomicNorms
