import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LPdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Introduce `l _ k _ _ hl d X p hSP hint R L lam hdet hlam`. Take `⟨s, c, a, hA⟩` from `hdet`. Establish `hprop` using `hSP.1`. Establish `nd : ∀ (n m : ℤ) (h : n + m = 2 * (d : ℤ)) (y : V l X m), (∀ x : V l X n, lam (cupV l X h x y) = 0) → y = 0`. Introduce `n m h y hy`.

Apply `hA m y` to reduce the goal to its premises. Introduce `t ht`. Take `rfl : c t = n` from `by omega`. Rewrite using `[R.comm X m (c t) _ ht h, Units.smul_def, map_zsmul, hy, smul_zero]`. Establish `fd : ∀ n, FiniteDimensional ℚ_[l] (V l X n)`.

Introduce `n`. Set `f : V l X n →ₗ[ℚ_[l]] (Fin s → ℚ_[l])` to `LinearMap.pi fun t => if h : n + c t = 2 * (d : ℤ) then lam ∘ₗ (cupV l X h).flip (a t) else 0`. Use `FiniteDimensional.of_injective f ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`.

Apply `hA n x` to reduce the goal to its premises. Introduce `t h`. Use `congrFun hx t` as an intermediate fact. Simplify `this` using `[f, h]`. Establish `van : ∀ n, 2 * (d : ℤ) < n → Subsingleton (V l X n)`.

Introduce `n hn`. Establish `key : ∀ z : V l X n, z = 0` using `fun z => hA n z (fun t h => by haveI := L.neg X (c t) (by omega)`. Rewrite using `[Subsingleton.elim (a t) 0]`. Use the proof step `simp)`. Conclude with `⟨fun x y => by rw [key x, key y]⟩`.

Establish `le : ∀ n m (h : n + m = 2 * (d : ℤ)), Module.finrank ℚ_[l] (V l X m) ≤ Module.finrank ℚ_[l] (V l X n)`. Introduce `n m h`. Use `haveI := fd n`. Use `haveI := fd m`. Establish `inj : Function.Injective ((cupV l X h).compr₂ lam).flip`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Conclude with `nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)`. Use `LinearMap.finrank_le_finrank_of_injective inj` as an intermediate fact. Rewrite `this` using `[Subspace.dual_finrank_eq]`. Then use the resulting hypothesis.

Establish `d0 : Module.finrank ℚ_[l] (V l X 0) ≤ 1`. Distinguish the cases in `hpt : Nonempty (Pt p)`. Take `⟨y0⟩` from `hpt`. Establish `hcon : ConnectedSpace X` using `connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected`. Establish `inj : Function.Injective (pb l y0.1 0)`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Apply `L.pts p hprop z` to reduce the goal to its premises. Introduce `y`. Rewrite using `[L.conn p hprop hcon z y y0, hz]`.

Establish `hsurj : Function.Surjective (LinearMap.toSpanSingleton ℚ_[l] _ (oneV l (S k)))`. Introduce `w`. Take `⟨r, hr, -⟩` from `L.line w`. Conclude with `⟨r, hr.symm⟩`. Use `haveI : Module.Finite ℚ_[l] (V l (S k) 0) := Module.Finite.of_surjective _ hsurj`.

Combine the equalities or inequalities in the displayed calculation. Establish `hz : ∀ z : V l X 0, z = 0` using `fun z => L.pts p hprop z (fun y => (hpt ⟨y⟩).elim) haveI : Subsingleton (V l X 0) := ⟨fun x y => by rw [hz x, hz y]⟩`. Simplify using `[Module.finrank_zero_of_subsingleton]`. Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : ∃ x, lam x ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hlam (LinearMap.ext hc)`. Establish `surj : Function.Surjective lam` using `fun r => ⟨(r / lam x0) • x0, by`. Rewrite using `[map_smul, smul_eq_mul, div_mul_cancel₀ _ hx0]⟩`. Use `haveI := fd (2 * (d : ℤ))`.

Establish `hnt : Nontrivial (V l X (2 * (d : ℤ)))` using `⟨⟨x0, 0, fun h => hx0 (by rw [h, map_zero])⟩⟩`. Establish `d2 : Module.finrank ℚ_[l] (V l X (2 * (d : ℤ))) = Module.finrank ℚ_[l] ℚ_[l]`. Rewrite using `[Module.finrank_self]`. Establish `h1` using `(le 0 (2 * (d : ℤ)) (zero_add _)).trans d0`. Establish `h2` using `Module.finrank_pos (R := ℚ_[l]) (M := V l X (2 * (d : ℤ)))`.

Use linear arithmetic over natural numbers and integers. Establish `inj : Function.Injective lam` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank d2).2 surj`. Use `⟨fd, van, LinearEquiv.ofBijective lam ⟨inj, surj⟩, fun n m h => ?_⟩` and prove the remaining obligations. Establish `htr : ((LinearEquiv.ofBijective lam ⟨inj, surj⟩ : V l X (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l]) : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] ℚ_[l]) = lam` using `LinearMap.ext fun x => rfl`. Rewrite using `[htr]`.

Use `haveI := fd n`. Use `haveI := fd m`. Establish `injf : Function.Injective ((cupV l X h).compr₂ lam).flip`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`.

Conclude with `nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)`. Establish `heq : Module.finrank ℚ_[l] (V l X m) = Module.finrank ℚ_[l] (V l X n →ₗ[ℚ_[l]] ℚ_[l])`. Rewrite using `[Subspace.dual_finrank_eq]`. Conclude with `le_antisymm (le n m h) (le m n (by omega))`. Conclude with `⟨injf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 injf⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.dualL_holds :
    UpperTheory.Gal.KunnethLefschetz.DualL := by
  intro l _ k _ _ hl d X p hSP hint R L lam hdet hlam
  obtain ⟨s, c, a, hA⟩ := hdet
  have hprop := hSP.1
  have nd : ∀ (n m : ℤ) (h : n + m = 2 * (d : ℤ)) (y : V l X m),
      (∀ x : V l X n, lam (cupV l X h x y) = 0) → y = 0 := by
    intro n m h y hy
    apply hA m y
    intro t ht
    obtain rfl : c t = n := by omega
    rw [R.comm X m (c t) _ ht h, Units.smul_def, map_zsmul, hy, smul_zero]
  have fd : ∀ n, FiniteDimensional ℚ_[l] (V l X n) := by
    intro n
    classical
    let f : V l X n →ₗ[ℚ_[l]] (Fin s → ℚ_[l]) := LinearMap.pi fun t =>
      if h : n + c t = 2 * (d : ℤ) then lam ∘ₗ (cupV l X h).flip (a t) else 0
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hA n x
    intro t h
    have := congrFun hx t
    simpa [f, h] using this
  have van : ∀ n, 2 * (d : ℤ) < n → Subsingleton (V l X n) := by
    intro n hn
    have key : ∀ z : V l X n, z = 0 := fun z => hA n z (fun t h => by
      haveI := L.neg X (c t) (by omega)
      rw [Subsingleton.elim (a t) 0]
      simp)
    exact ⟨fun x y => by rw [key x, key y]⟩
  have le : ∀ n m (h : n + m = 2 * (d : ℤ)),
      Module.finrank ℚ_[l] (V l X m) ≤ Module.finrank ℚ_[l] (V l X n) := by
    intro n m h
    haveI := fd n
    haveI := fd m
    have inj : Function.Injective ((cupV l X h).compr₂ lam).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
    have := LinearMap.finrank_le_finrank_of_injective inj
    rwa [Subspace.dual_finrank_eq] at this
  have d0 : Module.finrank ℚ_[l] (V l X 0) ≤ 1 := by
    by_cases hpt : Nonempty (Pt p)
    · obtain ⟨y0⟩ := hpt
      have hcon : ConnectedSpace X :=
        connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
      have inj : Function.Injective (pb l y0.1 0) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply L.pts p hprop z
        intro y
        rw [L.conn p hprop hcon z y y0, hz]
      have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℚ_[l] _ (oneV l (S k))) := by
        intro w
        obtain ⟨r, hr, -⟩ := L.line w
        exact ⟨r, hr.symm⟩
      haveI : Module.Finite ℚ_[l] (V l (S k) 0) := Module.Finite.of_surjective _ hsurj
      calc Module.finrank ℚ_[l] (V l X 0) ≤ Module.finrank ℚ_[l] (V l (S k) 0) :=
            LinearMap.finrank_le_finrank_of_injective inj
        _ ≤ 1 := finrank_le_one (oneV l (S k)) (fun w => (L.line w).exists.imp fun r hr => hr.symm)
    · have hz : ∀ z : V l X 0, z = 0 := fun z => L.pts p hprop z (fun y => (hpt ⟨y⟩).elim)
      haveI : Subsingleton (V l X 0) := ⟨fun x y => by rw [hz x, hz y]⟩
      simp [Module.finrank_zero_of_subsingleton]
  obtain ⟨x0, hx0⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hlam (LinearMap.ext hc)
  have surj : Function.Surjective lam := fun r => ⟨(r / lam x0) • x0, by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx0]⟩
  haveI := fd (2 * (d : ℤ))
  have hnt : Nontrivial (V l X (2 * (d : ℤ))) := ⟨⟨x0, 0, fun h => hx0 (by rw [h, map_zero])⟩⟩
  have d2 : Module.finrank ℚ_[l] (V l X (2 * (d : ℤ))) = Module.finrank ℚ_[l] ℚ_[l] := by
    rw [Module.finrank_self]
    have h1 := (le 0 (2 * (d : ℤ)) (zero_add _)).trans d0
    have h2 := Module.finrank_pos (R := ℚ_[l]) (M := V l X (2 * (d : ℤ)))
    omega
  have inj : Function.Injective lam := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d2).2 surj
  refine ⟨fd, van, LinearEquiv.ofBijective lam ⟨inj, surj⟩, fun n m h => ?_⟩
  have htr : ((LinearEquiv.ofBijective lam ⟨inj, surj⟩ : V l X (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l]) :
      V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] ℚ_[l]) = lam := LinearMap.ext fun x => rfl
  rw [htr]
  haveI := fd n
  haveI := fd m
  have injf : Function.Injective ((cupV l X h).compr₂ lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
  have heq : Module.finrank ℚ_[l] (V l X m) = Module.finrank ℚ_[l] (V l X n →ₗ[ℚ_[l]] ℚ_[l]) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm (le n m h) (le m n (by omega))
  exact ⟨injf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 injf⟩
