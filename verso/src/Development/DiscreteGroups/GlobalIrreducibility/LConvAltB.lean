import Development.DiscreteGroups.GlobalIrreducibility.LConvAltA

noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

/- English proof (translation)
Set `ρY : Representation ℂ G Y` to `{ toFun := fun h => (LinearMap.mulLeft ℂ (π h)).restrict (fun y hy => hY1 h y hy) map_one' := by`. Use `LinearMap.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Use `show π 1 * (y : H →L[ℂ] H) = y`. Rewrite using `[map_one, one_mul]`. Use the proof step `map_mul' := by`.

Introduce `a b`. Use `LinearMap.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Use `show π (a * b) * (y : H →L[ℂ] H) = π a * (π b * y)`. Rewrite using `[map_mul, mul_assoc] }`. Establish `hρY : ∀ h (y : Y), ((ρY h y : Y) : H →L[ℂ] H) = π h * y` using `fun h y => rfl`.

Set `Y'' : Submodule ℂ Y` to `Y'.comap Y.subtype`. Establish `hρY'' : ∀ h, Y'' ≤ Y''.comap (ρY h)` using `fun h y hy => hY'G h y hy`. Set `ρQ : Representation ℂ G (Y ⧸ Y'')` to `{ toFun := fun h => Y''.mapQ Y'' (ρY h) (hρY'' h) map_one' := by`. Use `Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Use `show Submodule.Quotient.mk (ρY 1 y) = Submodule.Quotient.mk y`.

Rewrite using `[map_one]`. Both sides reduce to the same expression. Use the proof step `map_mul' := by`. Introduce `a b`. Use `Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)` and prove the remaining obligations.

Use `show Submodule.Quotient.mk (ρY (a * b) y) = Submodule.Quotient.mk (ρY a (ρY b y))`. Rewrite using `[map_mul]`. Use `rfl }`. Establish `hρQ : ∀ h (y : Y), ρQ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρY h y)` using `fun h y => rfl`. Establish `hsm : IsSmooth ρQ`.

Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective Y'' q`. Take `⟨U, hUo, hU⟩` from `hSm y y.2`. Conclude with `alt_isOpen_fix ρQ _ U hUo fun v hv => by`. Rewrite using `[hρQ]`.

Use `congr 1`. Conclude with `Subtype.ext (hU v hv)`. Establish `hmk0 : ∀ y : Y, (Submodule.Quotient.mk y : Y ⧸ Y'') = 0 ↔ (y : H →L[ℂ] H) ∈ Y'` using `fun y => Submodule.Quotient.mk_eq_zero Y''`. Establish `hirr : ρQ.IsIrreducible`. Unfold `Representation.IsIrreducible`.

Rewrite using `[isSimpleOrder_iff]`. Use `⟨⟨⊥, ⊤, fun hbt => heY' ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk (⟨e, heY⟩ : Y) : Y ⧸ Y'') ∈ (⊥ : Subrepresentation ρQ).toSubmodule`. Rewrite using `[hbt]`. Conclude with `Submodule.mem_top`.

Conclude with `(hmk0 _).mp ((Submodule.mem_bot ℂ).mp h1)`. Set `Z : Submodule ℂ (H →L[ℂ] H)` to `(a.toSubmodule.comap Y''.mkQ).map Y.subtype`. Establish `hZY : Z ≤ Y` using `by rintro _ ⟨y, _, rfl⟩; exact y.2`. Establish `hZG : ∀ h, ∀ x ∈ Z, π h * x ∈ Z`. Introduce and unpack `h _ ⟨y, hy, rfl⟩`.

Conclude with `⟨ρY h y, a.apply_mem_toSubmodule h hy, rfl⟩`. Establish `hY'Z : Y' ≤ Z`. Introduce `x hx`. Use `⟨⟨x, hY'Y hx⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk _ ∈ a.toSubmodule`.

Rewrite using `[(hmk0 _).mpr hx]`. Conclude with `a.toSubmodule.zero_mem`. Distinguish the cases in `heZ : e ∈ Z`. Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Use `show a.toSubmodule = ⊤`. Use `eq_top_iff.mpr fun q _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective Y'' q`. Establish `hYZ : Y ≤ Z` using `hYs.trans (Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hZG h e heZ))`. Take `⟨y', hy', hyy⟩` from `hYZ y.2`.

Rewrite using `[← Subtype.ext hyy]`. Conclude with `hy'`. Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show a.toSubmodule = ⊥`.

Use `eq_bot_iff.mpr fun q hq => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective Y'' q`. Use `hmax Z hZY hZG heZ hY'Z ⟨y, hq, rfl⟩` as an intermediate fact. Conclude with `(Submodule.mem_bot ℂ).mpr ((hmk0 y).mpr this)`. Take `⟨hfd, hfr⟩` from `hN (Y ⧸ Y'') ρQ hsm hirr`.

Set `f : G → (H →L[ℂ] H)` to `fun h => e * π h * e`. Establish `hfY : ∀ a, ∀ y ∈ Y, f a * y ∈ Y` using `fun a y hy => by show e * π a * e * y ∈ Y`. Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `hYE _ (hY1 a _ (hYE y hy))`. Set `TY : G → Module.End ℂ Y` to `fun a => (LinearMap.mulLeft ℂ (f a)).restrict (fun y hy => hfY a y hy)`.

Establish `hTY'' : ∀ a, Y'' ≤ Y''.comap (TY a)` using `fun a y hy => by show e * π a * e * (y : H →L[ℂ] H) ∈ Y'`. Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `hY'E _ (hY'G a _ (hY'E _ hy))`. Set `T : G → Module.End ℂ (Y ⧸ Y'')` to `fun a => Y''.mapQ Y'' (TY a) (hTY'' a)`. Establish `hfixmk : ∀ y : Y, e * (y : H →L[ℂ] H) = y → Submodule.Quotient.mk y ∈ fixed ρQ K`.

Introduce `y hy`. Use `show ∀ κ : K, _`. Introduce `κ`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Rewrite using `[hρQ]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hρY, ← hy, ← mul_assoc, hKe' κ κ.2]`. Establish `hTW : ∀ a q, T a q ∈ fixed ρQ K`. Introduce `a q`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective Y'' q`. Conclude with `hfixmk (TY a y) (by show e * (e * π a * e * (y : H →L[ℂ] H)) = e * π a * e * y; simp only [← mul_assoc, hee])`. Use `hfd` as an intermediate fact. Set `t : G → Module.End ℂ (fixed ρQ K)` to `fun a => (T a).restrict (fun q _ => hTW a q)`. Establish `hdim : Module.finrank ℂ (Module.End ℂ (fixed ρQ K)) < d`.

Rewrite using `[Module.finrank_linearMap, ← sq]`. Conclude with `lt_of_le_of_lt (Nat.pow_le_pow_left hfr 2) hd`. Establish `h0` using `alt_std_eq_zero hdim fun i => t (g i)`. Establish `key : ∀ (l : List G) (w : fixed ρQ K), (((l.map t).prod w : fixed ρQ K) : Y ⧸ Y'') = (l.map T).prod w`. Introduce `l w`.

Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply]`. Conclude with `congrArg (T a) ih`.

Establish `key2 : ∀ (l : List G) (y : Y), (l.map T).prod (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((l.map TY).prod y)`. Introduce `l y`. Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]`.

Both sides reduce to the same expression. Establish `key3 : ∀ (l : List G) (y : Y), (((l.map TY).prod y : Y) : H →L[ℂ] H) = (l.map f).prod * y`. Introduce `l y`. Proceed by induction on `l with`. Consider the case `nil => simp`.

Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc, ← ih]`. Both sides reduce to the same expression. Set `e' : Y` to `⟨e, heY⟩`. Establish `he'W : Submodule.Quotient.mk e' ∈ fixed ρQ K` using `hfixmk e' hee`.

Establish `h1` using `congrArg (fun X : Module.End ℂ (fixed ρQ K) => ((X ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')) h0`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h1`. Establish `hsum : ∀ σ : Equiv.Perm (Fin d), (((List.ofFn fun i => t (g (σ i))).prod ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'') = Y''.mkQ (((List.ofFn fun i => g (σ i)).map TY).prod e')`. Introduce `σ`. Rewrite using `[show (List.ofFn fun i => t (g (σ i))) = (List.ofFn fun i => g (σ i)).map t by rw [List.map_ofFn]; rfl, key, key2]`.

Both sides reduce to the same expression. Establish `h1' : Y''.mkQ (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun i => g (σ i)).map TY).prod e') = 0`. Rewrite using `[map_sum]`. Use `(Finset.sum_congr rfl fun σ _ => ?_).trans h1` and prove the remaining obligations. Rewrite using `[map_smul, hsum]`.

Establish `h2` using `(Submodule.Quotient.mk_eq_zero Y'').mp h1'`. Establish `h3 : ((∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun i => g (σ i)).map TY).prod e' : Y) : H →L[ℂ] H) = (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e`. Rewrite using `[Submodule.coe_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, key3, smul_mul_assoc, show (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f by rw [List.map_ofFn]; rfl]`.

Rewrite using `[← h3]`. Conclude with `h2`.
-/
theorem alt_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G) (N : ℕ)
    (hN : UnifAdm G K N) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (hKe' : ∀ κ ∈ K, π κ * e = e) (hee : e * e = e)
    (Y Y' : Submodule ℂ (H →L[ℂ] H))
    (hYs : Y ≤ Submodule.span ℂ (Set.range fun h => π h * e)) (heY : e ∈ Y)
    (hY1 : ∀ h, ∀ y ∈ Y, π h * y ∈ Y) (hYE : ∀ y ∈ Y, e * y ∈ Y)
    (hSm : ∀ y ∈ Y, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u * y = y)
    (hY'Y : Y' ≤ Y) (hY'G : ∀ h, ∀ y ∈ Y', π h * y ∈ Y') (hY'E : ∀ y ∈ Y', e * y ∈ Y') (heY' : e ∉ Y')
    (hmax : ∀ Z : Submodule ℂ (H →L[ℂ] H), Z ≤ Y → (∀ h, ∀ z ∈ Z, π h * z ∈ Z) → e ∉ Z → Y' ≤ Z → Z ≤ Y')
    (d : ℕ) (hd : N ^ 2 < d) (g : Fin d → G) :
    (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e ∈ Y' := by
  let ρY : Representation ℂ G Y :=
    { toFun := fun h => (LinearMap.mulLeft ℂ (π h)).restrict (fun y hy => hY1 h y hy)
      map_one' := by
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π 1 * (y : H →L[ℂ] H) = y
        rw [map_one, one_mul]
      map_mul' := by
        intro a b
        refine LinearMap.ext fun y => Subtype.ext ?_
        show π (a * b) * (y : H →L[ℂ] H) = π a * (π b * y)
        rw [map_mul, mul_assoc] }
  have hρY : ∀ h (y : Y), ((ρY h y : Y) : H →L[ℂ] H) = π h * y := fun h y => rfl
  let Y'' : Submodule ℂ Y := Y'.comap Y.subtype
  have hρY'' : ∀ h, Y'' ≤ Y''.comap (ρY h) := fun h y hy => hY'G h y hy
  let ρQ : Representation ℂ G (Y ⧸ Y'') :=
    { toFun := fun h => Y''.mapQ Y'' (ρY h) (hρY'' h)
      map_one' := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY 1 y) = Submodule.Quotient.mk y
        rw [map_one]; rfl
      map_mul' := by
        intro a b
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        show Submodule.Quotient.mk (ρY (a * b) y) = Submodule.Quotient.mk (ρY a (ρY b y))
        rw [map_mul]; rfl }
  have hρQ : ∀ h (y : Y), ρQ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρY h y) := fun h y => rfl
  have hsm : IsSmooth ρQ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    obtain ⟨U, hUo, hU⟩ := hSm y y.2
    exact alt_isOpen_fix ρQ _ U hUo fun v hv => by
      rw [hρQ]; congr 1; exact Subtype.ext (hU v hv)
  have hmk0 : ∀ y : Y, (Submodule.Quotient.mk y : Y ⧸ Y'') = 0 ↔ (y : H →L[ℂ] H) ∈ Y' :=
    fun y => Submodule.Quotient.mk_eq_zero Y''
  have hirr : ρQ.IsIrreducible := by
    unfold Representation.IsIrreducible
    rw [isSimpleOrder_iff]
    refine ⟨⟨⊥, ⊤, fun hbt => heY' ?_⟩, fun a => ?_⟩
    · have h1 : (Submodule.Quotient.mk (⟨e, heY⟩ : Y) : Y ⧸ Y'') ∈ (⊥ : Subrepresentation ρQ).toSubmodule := by
        rw [hbt]; exact Submodule.mem_top
      exact (hmk0 _).mp ((Submodule.mem_bot ℂ).mp h1)
    · let Z : Submodule ℂ (H →L[ℂ] H) := (a.toSubmodule.comap Y''.mkQ).map Y.subtype
      have hZY : Z ≤ Y := by rintro _ ⟨y, _, rfl⟩; exact y.2
      have hZG : ∀ h, ∀ x ∈ Z, π h * x ∈ Z := by
        rintro h _ ⟨y, hy, rfl⟩
        exact ⟨ρY h y, a.apply_mem_toSubmodule h hy, rfl⟩
      have hY'Z : Y' ≤ Z := by
        intro x hx
        refine ⟨⟨x, hY'Y hx⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ a.toSubmodule
        rw [(hmk0 _).mpr hx]
        exact a.toSubmodule.zero_mem
      by_cases heZ : e ∈ Z
      · right
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊤
        refine eq_top_iff.mpr fun q _ => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have hYZ : Y ≤ Z := hYs.trans (Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hZG h e heZ))
        obtain ⟨y', hy', hyy⟩ := hYZ y.2
        rw [← Subtype.ext hyy]
        exact hy'
      · left
        apply Subrepresentation.toSubmodule_injective
        show a.toSubmodule = ⊥
        refine eq_bot_iff.mpr fun q hq => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
        have := hmax Z hZY hZG heZ hY'Z ⟨y, hq, rfl⟩
        exact (Submodule.mem_bot ℂ).mpr ((hmk0 y).mpr this)
  obtain ⟨hfd, hfr⟩ := hN (Y ⧸ Y'') ρQ hsm hirr
  let f : G → (H →L[ℂ] H) := fun h => e * π h * e
  have hfY : ∀ a, ∀ y ∈ Y, f a * y ∈ Y := fun a y hy => by
    show e * π a * e * y ∈ Y
    rw [mul_assoc, mul_assoc]; exact hYE _ (hY1 a _ (hYE y hy))
  let TY : G → Module.End ℂ Y := fun a => (LinearMap.mulLeft ℂ (f a)).restrict (fun y hy => hfY a y hy)
  have hTY'' : ∀ a, Y'' ≤ Y''.comap (TY a) := fun a y hy => by
    show e * π a * e * (y : H →L[ℂ] H) ∈ Y'
    rw [mul_assoc, mul_assoc]; exact hY'E _ (hY'G a _ (hY'E _ hy))
  let T : G → Module.End ℂ (Y ⧸ Y'') := fun a => Y''.mapQ Y'' (TY a) (hTY'' a)
  have hfixmk : ∀ y : Y, e * (y : H →L[ℂ] H) = y → Submodule.Quotient.mk y ∈ fixed ρQ K := by
    intro y hy
    show ∀ κ : K, _
    intro κ
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [hρQ]; congr 1; apply Subtype.ext
    rw [hρY, ← hy, ← mul_assoc, hKe' κ κ.2]
  have hTW : ∀ a q, T a q ∈ fixed ρQ K := by
    intro a q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Y'' q
    exact hfixmk (TY a y) (by show e * (e * π a * e * (y : H →L[ℂ] H)) = e * π a * e * y; simp only [← mul_assoc, hee])
  have := hfd
  let t : G → Module.End ℂ (fixed ρQ K) := fun a => (T a).restrict (fun q _ => hTW a q)
  have hdim : Module.finrank ℂ (Module.End ℂ (fixed ρQ K)) < d := by
    rw [Module.finrank_linearMap, ← sq]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hfr 2) hd
  have h0 := alt_std_eq_zero hdim fun i => t (g i)
  have key : ∀ (l : List G) (w : fixed ρQ K), (((l.map t).prod w : fixed ρQ K) : Y ⧸ Y'') = (l.map T).prod w := by
    intro l w
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact congrArg (T a) ih
  have key2 : ∀ (l : List G) (y : Y),
      (l.map T).prod (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((l.map TY).prod y) := by
    intro l y
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]; rfl
  have key3 : ∀ (l : List G) (y : Y), (((l.map TY).prod y : Y) : H →L[ℂ] H) = (l.map f).prod * y := by
    intro l y
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc, ← ih]
      rfl
  let e' : Y := ⟨e, heY⟩
  have he'W : Submodule.Quotient.mk e' ∈ fixed ρQ K := hfixmk e' hee
  have h1 := congrArg (fun X : Module.End ℂ (fixed ρQ K) => ((X ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')) h0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] at h1
  have hsum : ∀ σ : Equiv.Perm (Fin d), (((List.ofFn fun i => t (g (σ i))).prod ⟨_, he'W⟩ : fixed ρQ K) : Y ⧸ Y'')
      = Y''.mkQ (((List.ofFn fun i => g (σ i)).map TY).prod e') := by
    intro σ
    rw [show (List.ofFn fun i => t (g (σ i))) = (List.ofFn fun i => g (σ i)).map t by rw [List.map_ofFn]; rfl,
      key, key2]
    rfl
  have h1' : Y''.mkQ (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e') = 0 := by
    rw [map_sum]
    refine (Finset.sum_congr rfl fun σ _ => ?_).trans h1
    rw [map_smul, hsum]
  have h2 := (Submodule.Quotient.mk_eq_zero Y'').mp h1'
  have h3 : ((∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn fun i => g (σ i)).map TY).prod e' : Y) : H →L[ℂ] H) =
      (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun i => e * π (g (σ i)) * e).prod) * e := by
    rw [Submodule.coe_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Submodule.coe_smul, key3, smul_mul_assoc,
      show (List.ofFn fun i => e * π (g (σ i)) * e) = (List.ofFn fun i => g (σ i)).map f by rw [List.map_ofFn]; rfl]
  rw [← h3]
  exact h2

end DiscreteGroups.sglob.LConv
