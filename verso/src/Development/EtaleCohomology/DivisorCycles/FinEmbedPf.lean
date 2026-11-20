import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.FinEmbedPf

section core
variable {K V U ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup U] [Module K U]

def SS {W : Type} [AddCommGroup W] [Module K W] (a : ι → W →ₗ[K] W) : Prop :=
  ∀ S : Submodule K W, (∀ i, ∀ v ∈ S, a i v ∈ S) → ∃ S' : Submodule K W, IsCompl S S' ∧ ∀ i, ∀ v ∈ S', a i v ∈ S'

def gens (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) : Set (V →ₗ[K] V) :=
  {F | ∃ (t' : U →ₗ[K] V) (t : V →ₗ[K] U), (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧
    F = t' ∘ₗ t}

/- English proof (translation)
Establish `hx` using `Submodule.projection_add_projection_eq_self h x`. Use `conv_lhs => rw [← hx]`. Rewrite using `[map_add, map_add, Submodule.projection_apply_of_mem_left h (hp _ (Submodule.projection_apply_mem h x)), Submodule.projection_apply_of_mem_right h (hq _ (Submodule.projection_apply_mem h.symm x)), add_zero]`.
-/
theorem proj_comm {E : Type} [AddCommGroup E] [Module K E] (p q : Submodule K E) (h : IsCompl p q)
    (φ : E →ₗ[K] E) (hp : ∀ v ∈ p, φ v ∈ p) (hq : ∀ v ∈ q, φ v ∈ q) (x : E) :
    p.projection q h (φ x) = φ (p.projection q h x) := by
  have hx := Submodule.projection_add_projection_eq_self h x
  conv_lhs => rw [← hx]
  rw [map_add, map_add, Submodule.projection_apply_of_mem_left h (hp _ (Submodule.projection_apply_mem h x)),
    Submodule.projection_apply_of_mem_right h (hq _ (Submodule.projection_apply_mem h.symm x)), add_zero]

/- English proof (translation)
Use `set P : V →ₗ[K] V := LinearMap.id - E with hPdef`. Establish `hP : ∀ x, P x = x - E x` using `fun x => rfl`. Establish `hEP : ∀ x, E (P x) = 0` using `fun x => by rw [hP, map_sub, hEi, sub_self]`. Establish `hPE : ∀ x, P (E x) = 0` using `fun x => by rw [hP, hEi, sub_self]`. Establish `hPP : ∀ x, P (P x) = P x` using `fun x => by rw [hP (P x), hEP, sub_zero]`.

Establish `hPc : ∀ i x, P (a i x) = a i (P x)` using `fun i x => by rw [hP, hP, hEc, map_sub]`. Choose the witnesses or unpack the hypotheses as in `⟨t', ht', hPt'⟩ : ∃ t' : U →ₗ[K] V, (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ P ∘ₗ t' ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0` using `hspan P hcon`.

Apply `hker` to reduce the goal to its premises. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `m hm`. Use `congrArg (fun f => f m) h0` as an intermediate fact. Simplify `this` using `[hP, hm]`.

Use `set M : U →ₗ[K] V := P ∘ₗ t' with hMdef`. Establish `hMc : ∀ i u, a i (M u) = M (b i u)` using `fun i u => by`. Simplify using `only [hMdef, LinearMap.comp_apply]`. Rewrite using `[← hPc]`. Use `congr 1`.

Conclude with `congrArg (fun f => f u) (ht' i)`. Establish `hEM : ∀ u, E (M u) = 0` using `fun u => hEP _`. Establish `hPM : ∀ u, P (M u) = M u` using `fun u => hPP _`. Take `⟨Cc, hC, hCs⟩` from `hU (LinearMap.ker M) (fun i v hv => by`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[← hMc, hv, map_zero])`. Establish `hinj : ∀ c ∈ Cc, M c = 0 → c = 0` using `fun c hc h0 => by`. Establish `: c ∈ LinearMap.ker M ⊓ Cc` using `⟨h0, hc⟩`. Rewrite `this` using `[hC.inf_eq_bot]`. Conclude with `this`.

Use `set R : Submodule K V := Submodule.map M Cc with hRdef`. Take `⟨D, hD, hDs⟩` from `hV R (fun i v hv => by`. Take `⟨c, hc, rfl⟩` from `hv`. Conclude with `⟨b i c, hCs i c hc, (hMc i c).symm⟩)`. Establish `hinj' : Function.Injective (M ∘ₗ Cc.subtype)`.

Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Use `hinj (x - y) (Cc.sub_mem x.2 y.2) (by simpa [sub_eq_zero] using hxy)` as an intermediate fact. Conclude with `sub_eq_zero.mp this`. Establish `hRr : LinearMap.range (M ∘ₗ Cc.subtype) = R`.

Use extensionality with `y`. Simplify using `[hRdef, Submodule.mem_map]`. Set `e` to `LinearEquiv.ofInjective (M ∘ₗ Cc.subtype) hinj'`. Set `T : V →ₗ[K] U` to `Cc.subtype ∘ₗ e.symm.toLinearMap ∘ₗ (LinearEquiv.ofEq _ _ hRr.symm).toLinearMap ∘ₗ R.projectionOnto D hD`. Establish `hTC : ∀ v, T v ∈ Cc` using `fun v => (e.symm _).2`.

Establish `hMT : ∀ v, M (T v) = R.projection D hD v` using `fun v => by`. Use `congrArg Subtype.val (e.apply_symm_apply ((LinearEquiv.ofEq _ _ hRr.symm).toLinearMap (R.projectionOnto D hD v)))` as an intermediate fact. Rewrite `this` using `[LinearEquiv.ofInjective_apply]`. Simplify `this` using `[T]`. Establish `hpc : ∀ i v, R.projection D hD (a i v) = a i (R.projection D hD v)` using `fun i v => proj_comm R D hD (a i) (fun w hw => by`.

Take `⟨c, hc, rfl⟩` from `hw`. Conclude with `⟨b i c, hCs i c hc, (hMc i c).symm⟩) (hDs i) v`. Establish `hTc : ∀ i v, T (a i v) = b i (T v)` using `fun i v => by`. Establish `h1` using `hinj (T (a i v) - b i (T v)) (Cc.sub_mem (hTC _) (hCs i _ (hTC v))) (by rw [map_sub, hMT, ← hMc, hMT, hpc, sub_self])`. Conclude with `sub_eq_zero.mp h1`.

Use `set H : V →ₗ[K] V := M ∘ₗ (T ∘ₗ P) with hHdef`. Establish `hH : ∀ x, H x = R.projection D hD (P x)` using `fun x => hMT _`. Establish `hHgen : H ∈ gens a b` using `⟨M, T ∘ₗ P, fun i => LinearMap.ext fun u => by simp [hMc], fun i => LinearMap.ext fun v => by simp [hPc, hTc], rfl⟩`. Establish `hprojR : ∀ x, R.projection D hD x ∈ R` using `fun x => Submodule.projection_apply_mem hD x`. Establish `hER : ∀ y ∈ R, E y = 0` using `fun y hy => by`.

Take `⟨c, _, rfl⟩` from `hy`. Conclude with `hEM c`. Establish `hPR : ∀ y ∈ R, P y = y` using `fun y hy => by rw [hP, hER y hy, sub_zero]`. Establish `hEH : ∀ x, E (H x) = 0` using `fun x => by rw [hH]; exact hER _ (hprojR _)`. Establish `hHE : ∀ x, H (E x) = 0` using `fun x => by rw [hH, hPE, map_zero]`.

Establish `hHH : ∀ x, H (H x) = H x` using `fun x => by`. Rewrite using `[hH (H x), hPR _ (by rw [hH]; exact hprojR _), hH, Submodule.projection_apply_of_mem_left hD (hprojR _)]`. Use `⟨E + H, Submodule.add_mem _ hE (Submodule.subset_span hHgen), fun x => ?_, fun i x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, map_add, hEi, hEH, hHE, hHH, add_zero, zero_add]`. Simplify using `only [LinearMap.add_apply, map_add, hEc, hH, hPc, hpc]`.

Establish `hle : LinearMap.ker (E + H) ≤ LinearMap.ker E` using `fun x hx => by`. Rewrite `hx` using `[LinearMap.mem_ker, LinearMap.add_apply]`. Use `congrArg E hx` as an intermediate fact. Rewrite `this` using `[map_add, hEi, hEH, add_zero, map_zero]`. Conclude with `this`.

Use `lt_of_le_of_ne hle (fun heq => ?_)` and prove the remaining obligations. Establish `hRne : ∃ c ∈ Cc, M c ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `hPt'` to reduce the goal to its premises.

Use extensionality with `u`. Establish `hu : u ∈ LinearMap.ker M ⊔ Cc` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨k, hk, c, hc', rfl⟩` from `Submodule.mem_sup.mp hu`. Use `show M (k + c) = 0`. Rewrite using `[map_add, LinearMap.mem_ker.mp hk, hc c hc', add_zero]`.

Take `⟨c, hc, hne⟩` from `hRne`. Establish `hyR : M c ∈ R` using `⟨c, hc, rfl⟩`. Establish `hy : M c ∈ LinearMap.ker E` using `hEM c`. Rewrite `hy` using `[← heq, LinearMap.mem_ker, LinearMap.add_apply, hEM, zero_add, hH, hPR _ hyR, Submodule.projection_apply_of_mem_left hD hyR]`. Conclude with `hne hy`.
-/
theorem step (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0)
    (E : V →ₗ[K] V) (hE : E ∈ Submodule.span K (gens a b)) (hEi : ∀ x, E (E x) = E x)
    (hEc : ∀ i x, E (a i x) = a i (E x)) (hker : LinearMap.ker E ≠ ⊥) :
    ∃ E' : V →ₗ[K] V, E' ∈ Submodule.span K (gens a b) ∧ (∀ x, E' (E' x) = E' x) ∧
      (∀ i x, E' (a i x) = a i (E' x)) ∧ LinearMap.ker E' < LinearMap.ker E := by
  set P : V →ₗ[K] V := LinearMap.id - E with hPdef
  have hP : ∀ x, P x = x - E x := fun x => rfl
  have hEP : ∀ x, E (P x) = 0 := fun x => by rw [hP, map_sub, hEi, sub_self]
  have hPE : ∀ x, P (E x) = 0 := fun x => by rw [hP, hEi, sub_self]
  have hPP : ∀ x, P (P x) = P x := fun x => by rw [hP (P x), hEP, sub_zero]
  have hPc : ∀ i x, P (a i x) = a i (P x) := fun i x => by rw [hP, hP, hEc, map_sub]
  obtain ⟨t', ht', hPt'⟩ : ∃ t' : U →ₗ[K] V, (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ P ∘ₗ t' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hspan P hcon
    apply hker
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := congrArg (fun f => f m) h0
    simpa [hP, hm] using this
  set M : U →ₗ[K] V := P ∘ₗ t' with hMdef
  have hMc : ∀ i u, a i (M u) = M (b i u) := fun i u => by
    simp only [hMdef, LinearMap.comp_apply]
    rw [← hPc]; congr 1; exact congrArg (fun f => f u) (ht' i)
  have hEM : ∀ u, E (M u) = 0 := fun u => hEP _
  have hPM : ∀ u, P (M u) = M u := fun u => hPP _
  obtain ⟨Cc, hC, hCs⟩ := hU (LinearMap.ker M) (fun i v hv => by
    rw [LinearMap.mem_ker] at hv ⊢; rw [← hMc, hv, map_zero])
  have hinj : ∀ c ∈ Cc, M c = 0 → c = 0 := fun c hc h0 => by
    have : c ∈ LinearMap.ker M ⊓ Cc := ⟨h0, hc⟩
    rw [hC.inf_eq_bot] at this; exact this
  set R : Submodule K V := Submodule.map M Cc with hRdef
  obtain ⟨D, hD, hDs⟩ := hV R (fun i v hv => by
    obtain ⟨c, hc, rfl⟩ := hv
    exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩)
  have hinj' : Function.Injective (M ∘ₗ Cc.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have := hinj (x - y) (Cc.sub_mem x.2 y.2) (by simpa [sub_eq_zero] using hxy)
    exact sub_eq_zero.mp this
  have hRr : LinearMap.range (M ∘ₗ Cc.subtype) = R := by
    ext y; simp [hRdef, Submodule.mem_map]
  let e := LinearEquiv.ofInjective (M ∘ₗ Cc.subtype) hinj'
  let T : V →ₗ[K] U := Cc.subtype ∘ₗ e.symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ hRr.symm).toLinearMap ∘ₗ R.projectionOnto D hD
  have hTC : ∀ v, T v ∈ Cc := fun v => (e.symm _).2
  have hMT : ∀ v, M (T v) = R.projection D hD v := fun v => by
    have := congrArg Subtype.val (e.apply_symm_apply
      ((LinearEquiv.ofEq _ _ hRr.symm).toLinearMap (R.projectionOnto D hD v)))
    rw [LinearEquiv.ofInjective_apply] at this
    simpa [T] using this
  have hpc : ∀ i v, R.projection D hD (a i v) = a i (R.projection D hD v) := fun i v =>
    proj_comm R D hD (a i) (fun w hw => by
      obtain ⟨c, hc, rfl⟩ := hw
      exact ⟨b i c, hCs i c hc, (hMc i c).symm⟩) (hDs i) v
  have hTc : ∀ i v, T (a i v) = b i (T v) := fun i v => by
    have h1 := hinj (T (a i v) - b i (T v)) (Cc.sub_mem (hTC _) (hCs i _ (hTC v)))
      (by rw [map_sub, hMT, ← hMc, hMT, hpc, sub_self])
    exact sub_eq_zero.mp h1
  set H : V →ₗ[K] V := M ∘ₗ (T ∘ₗ P) with hHdef
  have hH : ∀ x, H x = R.projection D hD (P x) := fun x => hMT _
  have hHgen : H ∈ gens a b := ⟨M, T ∘ₗ P, fun i => LinearMap.ext fun u => by simp [hMc],
    fun i => LinearMap.ext fun v => by simp [hPc, hTc], rfl⟩
  have hprojR : ∀ x, R.projection D hD x ∈ R := fun x => Submodule.projection_apply_mem hD x
  have hER : ∀ y ∈ R, E y = 0 := fun y hy => by
    obtain ⟨c, _, rfl⟩ := hy; exact hEM c
  have hPR : ∀ y ∈ R, P y = y := fun y hy => by rw [hP, hER y hy, sub_zero]
  have hEH : ∀ x, E (H x) = 0 := fun x => by rw [hH]; exact hER _ (hprojR _)
  have hHE : ∀ x, H (E x) = 0 := fun x => by rw [hH, hPE, map_zero]
  have hHH : ∀ x, H (H x) = H x := fun x => by
    rw [hH (H x), hPR _ (by rw [hH]; exact hprojR _), hH,
      Submodule.projection_apply_of_mem_left hD (hprojR _)]
  refine ⟨E + H, Submodule.add_mem _ hE (Submodule.subset_span hHgen), fun x => ?_, fun i x => ?_, ?_⟩
  · simp only [LinearMap.add_apply, map_add, hEi, hEH, hHE, hHH, add_zero, zero_add]
  · simp only [LinearMap.add_apply, map_add, hEc, hH, hPc, hpc]
  · have hle : LinearMap.ker (E + H) ≤ LinearMap.ker E := fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.add_apply] at hx
      have := congrArg E hx
      rw [map_add, hEi, hEH, add_zero, map_zero] at this
      exact this
    refine lt_of_le_of_ne hle (fun heq => ?_)
    have hRne : ∃ c ∈ Cc, M c ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hPt'
      ext u
      have hu : u ∈ LinearMap.ker M ⊔ Cc := by rw [hC.sup_eq_top]; trivial
      obtain ⟨k, hk, c, hc', rfl⟩ := Submodule.mem_sup.mp hu
      show M (k + c) = 0
      rw [map_add, LinearMap.mem_ker.mp hk, hc c hc', add_zero]
    obtain ⟨c, hc, hne⟩ := hRne
    have hyR : M c ∈ R := ⟨c, hc, rfl⟩
    have hy : M c ∈ LinearMap.ker E := hEM c
    rw [← heq, LinearMap.mem_ker, LinearMap.add_apply, hEM, zero_add, hH, hPR _ hyR,
      Submodule.projection_apply_of_mem_left hD hyR] at hy
    exact hne hy

/- English proof (translation)
Establish `key : ∀ d : ℕ, ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) → (∀ i x, E (a i x) = a i (E x)) → Module.finrank K (LinearMap.ker E) ≤ d → (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b)`. Establish `fin : ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) → LinearMap.ker E = ⊥ → (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b)`. Introduce `E hE hi hk`. Establish `: E = LinearMap.id`. Use extensionality with `x`.

Establish `h1 : E (E x - x) = 0` using `by rw [map_sub, hi, sub_self]`. Use `(LinearMap.ker_eq_bot'.mp hk) _ h1` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Rewrite using `[← this]`. Conclude with `hE`.

Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `E hE hi _ hd`. Conclude with `fin E hE hi (Submodule.finrank_eq_zero.mp (by omega))`.

Consider the case `succ d ih`. Introduce `E hE hi hc hd`. Distinguish the cases in `hk : LinearMap.ker E = ⊥`. Conclude with `fin E hE hi hk`. Take `⟨E', hE', hi', hc', hlt⟩` from `step a b hV hU hspan E hE hi hc hk`.

Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact. Conclude with `ih E' hE' hi' hc' (by omega)`. Conclude with `key _ 0 (Submodule.zero_mem _) (fun x => by simp) (fun i x => by simp) (Submodule.finrank_le _)`.
-/
theorem main (a : ι → V →ₗ[K] V) (b : ι → U →ₗ[K] U) (hV : SS a) (hU : SS b)
    (hspan : ∀ Z : V →ₗ[K] V, (∀ t : U →ₗ[K] V, (∀ i, a i ∘ₗ t = t ∘ₗ b i) → Z ∘ₗ t = 0) → Z = 0) :
    (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
  have key : ∀ d : ℕ, ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
      (∀ i x, E (a i x) = a i (E x)) → Module.finrank K (LinearMap.ker E) ≤ d →
      (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
    have fin : ∀ E : V →ₗ[K] V, E ∈ Submodule.span K (gens a b) → (∀ x, E (E x) = E x) →
        LinearMap.ker E = ⊥ → (LinearMap.id : V →ₗ[K] V) ∈ Submodule.span K (gens a b) := by
      intro E hE hi hk
      have : E = LinearMap.id := by
        ext x
        have h1 : E (E x - x) = 0 := by rw [map_sub, hi, sub_self]
        have := (LinearMap.ker_eq_bot'.mp hk) _ h1
        simpa [sub_eq_zero] using this
      rw [← this]; exact hE
    intro d
    induction d with
    | zero =>
      intro E hE hi _ hd
      exact fin E hE hi (Submodule.finrank_eq_zero.mp (by omega))
    | succ d ih =>
      intro E hE hi hc hd
      by_cases hk : LinearMap.ker E = ⊥
      · exact fin E hE hi hk
      · obtain ⟨E', hE', hi', hc', hlt⟩ := step a b hV hU hspan E hE hi hc hk
        have := Submodule.finrank_lt_finrank_of_lt hlt
        exact ih E' hE' hi' hc' (by omega)
  exact key _ 0 (Submodule.zero_mem _) (fun x => by simp) (fun i x => by simp)
    (Submodule.finrank_le _)

end core

/- English proof (translation)
Introduce `Γ K _ _ N n ρ r A B hSub hρ hr`. Set `a : Γ → (Fin N → K) →ₗ[K] (Fin N → K)` to `fun g => Matrix.toLin' (ρ g : Mat K N)`. Set `b : Γ → (Fin n → K) →ₗ[K] (Fin n → K)` to `fun g => Matrix.toLin' (r g : Mat K n)`. Establish `hV : SS a` using `fun S hS => by`. Take `⟨S', h1, h2⟩` from `hρ S (fun g v hv => by simpa [a, Matrix.toLin'_apply] using hS g v hv)`.

Conclude with `⟨S', h1, fun g v hv => by simpa [a, Matrix.toLin'_apply] using h2 g v hv⟩`. Establish `hU : SS b` using `fun S hS => by`. Take `⟨S', h1, h2⟩` from `hr S (fun g v hv => by simpa [b, Matrix.toLin'_apply] using hS g v hv)`. Conclude with `⟨S', h1, fun g v hv => by simpa [b, Matrix.toLin'_apply] using h2 g v hv⟩`. Establish `hspan : ∀ Z : (Fin N → K) →ₗ[K] (Fin N → K), (∀ t : (Fin n → K) →ₗ[K] (Fin N → K), (∀ g, a g ∘ₗ t = t ∘ₗ b g) → Z ∘ₗ t = 0) → Z = 0`.

Introduce `Z hZ`. Establish `h0` using `hSub.2.2 (LinearMap.toMatrix' Z) (fun T hT => by`. Use `hZ (Matrix.toLin' T) (fun g => by` as an intermediate fact. Simplify using `only [a, b, ← Matrix.toLin'_mul, hT g])`. Use `congrArg LinearMap.toMatrix' this` as an intermediate fact.

Simplify `this)` using `[LinearMap.toMatrix'_comp]`. Use `congrArg Matrix.toLin' h0` as an intermediate fact. Simplify using `using this`. Establish `hid` using `main a b hV hU hspan`. Take `⟨k, f, g, hsum⟩` from `Submodule.mem_span_set'.mp hid`.

Establish `hg : ∀ j, ∃ (t' : (Fin n → K) →ₗ[K] (Fin N → K)) (t : (Fin N → K) →ₗ[K] (Fin n → K)), (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧ (g j : _) = t' ∘ₗ t` using `fun j => (g j).2`. Use `choose t' t ht' ht hEq using hg`. Use `⟨k, fun j => LinearMap.toMatrix' (t j), fun j => f j • LinearMap.toMatrix' (t' j), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j g`. Use `congrArg LinearMap.toMatrix' (ht j g)` as an intermediate fact.

Simplify `this` using `[a, b, LinearMap.toMatrix'_comp]`. Introduce `j g`. Use `congrArg LinearMap.toMatrix' (ht' j g)` as an intermediate fact. Simplify using `only [a, b, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at this`. Rewrite using `[Matrix.mul_smul, smul_mul, this]`.

Establish `h1 : ∑ j, f j • (t' j ∘ₗ t j) = LinearMap.id`. Rewrite using `[← hsum]; exact Finset.sum_congr rfl fun j _ => by rw [hEq]`. Establish `h2` using `congrArg LinearMap.toMatrix' h1`. Rewrite `h2` using `[map_sum, LinearMap.toMatrix'_id]`. Rewrite using `[← h2]`.

Conclude with `Finset.sum_congr rfl fun j _ => by`. Rewrite using `[map_smul, LinearMap.toMatrix'_comp, smul_mul]`.
-/
theorem FinEmbed_of : FinEmbed := by
  intro Γ K _ _ N n ρ r A B hSub hρ hr
  let a : Γ → (Fin N → K) →ₗ[K] (Fin N → K) := fun g => Matrix.toLin' (ρ g : Mat K N)
  let b : Γ → (Fin n → K) →ₗ[K] (Fin n → K) := fun g => Matrix.toLin' (r g : Mat K n)
  have hV : SS a := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hρ S (fun g v hv => by simpa [a, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [a, Matrix.toLin'_apply] using h2 g v hv⟩
  have hU : SS b := fun S hS => by
    obtain ⟨S', h1, h2⟩ := hr S (fun g v hv => by simpa [b, Matrix.toLin'_apply] using hS g v hv)
    exact ⟨S', h1, fun g v hv => by simpa [b, Matrix.toLin'_apply] using h2 g v hv⟩
  have hspan : ∀ Z : (Fin N → K) →ₗ[K] (Fin N → K),
      (∀ t : (Fin n → K) →ₗ[K] (Fin N → K), (∀ g, a g ∘ₗ t = t ∘ₗ b g) → Z ∘ₗ t = 0) → Z = 0 := by
    intro Z hZ
    have h0 := hSub.2.2 (LinearMap.toMatrix' Z) (fun T hT => by
      have := hZ (Matrix.toLin' T) (fun g => by
        simp only [a, b, ← Matrix.toLin'_mul, hT g])
      have := congrArg LinearMap.toMatrix' this
      simpa [LinearMap.toMatrix'_comp] using this)
    have := congrArg Matrix.toLin' h0
    simpa using this
  have hid := main a b hV hU hspan
  obtain ⟨k, f, g, hsum⟩ := Submodule.mem_span_set'.mp hid
  have hg : ∀ j, ∃ (t' : (Fin n → K) →ₗ[K] (Fin N → K)) (t : (Fin N → K) →ₗ[K] (Fin n → K)),
      (∀ i, a i ∘ₗ t' = t' ∘ₗ b i) ∧ (∀ i, t ∘ₗ a i = b i ∘ₗ t) ∧ (g j : _) = t' ∘ₗ t := fun j => (g j).2
  choose t' t ht' ht hEq using hg
  refine ⟨k, fun j => LinearMap.toMatrix' (t j), fun j => f j • LinearMap.toMatrix' (t' j), ?_, ?_, ?_⟩
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht j g)
    simpa [a, b, LinearMap.toMatrix'_comp] using this
  · intro j g
    have := congrArg LinearMap.toMatrix' (ht' j g)
    simp only [a, b, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at this
    rw [Matrix.mul_smul, smul_mul, this]
  · have h1 : ∑ j, f j • (t' j ∘ₗ t j) = LinearMap.id := by
      rw [← hsum]; exact Finset.sum_congr rfl fun j _ => by rw [hEq]
    have h2 := congrArg LinearMap.toMatrix' h1
    rw [map_sum, LinearMap.toMatrix'_id] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, LinearMap.toMatrix'_comp, smul_mul]

end LateralTheory.DivDb.FinEmbedPf
