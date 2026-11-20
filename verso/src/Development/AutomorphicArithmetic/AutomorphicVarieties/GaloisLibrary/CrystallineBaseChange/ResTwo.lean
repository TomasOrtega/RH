import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

open UpperTheory.V UpperTheory.V.Af

/- English proof (translation)
Take `⟨hne, -, hmin⟩` from `hirr`. Establish `hnt : Nontrivial (Fin n → k)`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_nontrivial_iff_subsingleton]`. Conclude with `hne (Subsingleton.elim _ _)`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))`. Use `⟨c, ?_⟩` and prove the remaining obligations. Break down `hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by` into its components or cases. Introduce `t v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`.

Rewrite using `[Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h`. Conclude with `absurd h hc`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c`.

Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hv` using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hv]`. Simplify using the standard rewrite rules.
-/
private theorem schur_scalar_of_commutes_irreducible {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : Matrix (Fin n) (Fin n) k)
    (hg : ∀ s, g * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * g) :
    ∃ c : k, g = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨hne, -, hmin⟩ := hirr
  have hnt : Nontrivial (Fin n → k) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))
  refine ⟨c, ?_⟩
  rcases hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by
      intro t v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c := by
      rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]; simp

/- English proof (translation)
Take `⟨g, hg⟩` from `hiso`. Establish `hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹`. Introduce `s hs`. Take `⟨x, rfl⟩` from `(h1 s).1 hs`. Conclude with `hg x`.

Distinguish the cases in `hall : ∀ s, δ s = 1`. Conclude with `Or.inl ⟨g, fun s => hH s (hall s)⟩`. Use `push Not at hall`. Take `⟨t, ht⟩` from `hall`. Establish `ht' : δ t = -1` using `(h2 t).resolve_left ht`.

Take `⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g` from `⟨_, rfl⟩`. Establish `hrt : r' t = g * (r t * u) * g⁻¹` using `by rw [hu]; group`. Establish `hcomm : ∀ s, δ s = 1 → u * r s = r s * u`. Introduce `s hs`. Establish `e1` using `hH s hs`.

Establish `e2` using `hH (t * s * t⁻¹) (by simp [hs])`. Simplify using `only [map_mul, map_inv] at e2`. Rewrite `e2` using `[e1, hrt]`. Establish `e3 : u * r s = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u` using `by group`. Rewrite using `[e3, e2]`.

Use `group`. Take `⟨c, hc⟩` from `schur_scalar_of_commutes_irreducible (r.comp φ) hirr (u : Matrix (Fin n) (Fin n) k) (by`. Introduce `x`. Use `hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)` as an intermediate fact. Simplify using `using congrArg Units.val this)`.

Establish `hcen : ∀ a : GL (Fin n) k, u * a = a * u`. Introduce `a`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[hc]`. Establish `huu : u * u = 1`.

Establish `e2` using `hH (t * t) (by simp [ht'])`. Simplify using `only [map_mul] at e2`. Rewrite `e2` using `[hrt]`. Establish `e3 : u * r t * u = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g` using `by group`. Rewrite `e3` using `[e2, hcen (r t)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹`. Introduce `s hs`. Establish `e1` using `hH (t⁻¹ * s) (by simp [hs, ht'])`. Establish `e2 : r' s = r' t * r' (t⁻¹ * s)` using `by rw [← map_mul]; simp`.

Rewrite using `[e2, e1, hrt, ← hcen (r t), map_mul, map_inv]`. Use `group`. Establish `hu2 : u = 1 ∨ u = -1`. Establish `e` using `congrArg Units.val huu`. Rewrite `e` using `[Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one]`.

Establish `hn : Nonempty (Fin n)`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_nonempty_iff]`. Conclude with `hirr.1 (Subsingleton.elim _ _)`. Take `⟨i⟩` from `hn`.

Establish `e'` using `congrFun (congrFun e i) i`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'`. Break down `mul_self_eq_one_iff.1 e' with h | h` into its components or cases. Use `left`. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `[hc, h]`. Use `right`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[hc, h]`. Break down `hu2 with h | h` into its components or cases.

Use `Or.inl ⟨g, fun s => ?_⟩` and prove the remaining obligations. Break down `h2 s with hs | hs` into its components or cases. Conclude with `hH s hs`. Rewrite using `[hneg s hs, h, one_mul]`. Use `Or.inr ⟨g, fun s => ?_⟩` and prove the remaining obligations.

Break down `h2 s with hs | hs` into its components or cases. Rewrite using `[hH s hs]`. Use `congr 2`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[tw_val, hs]`.

Rewrite using `[hneg s hs, h]`. Use `congr 2`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[tw_val, hs]`.
-/
private theorem part_two {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r r' : Γ →* GL (Fin n) k)
    (hirr : IsIrr (r.comp φ)) (hiso : RepIso (r.comp φ) (r'.comp φ)) : RepIso r r' ∨ RepIso (tw r δ) r' := by
  obtain ⟨g, hg⟩ := hiso
  have hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹ := by
    intro s hs
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hg x
  by_cases hall : ∀ s, δ s = 1
  · exact Or.inl ⟨g, fun s => hH s (hall s)⟩
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g := ⟨_, rfl⟩
  have hrt : r' t = g * (r t * u) * g⁻¹ := by rw [hu]; group
  have hcomm : ∀ s, δ s = 1 → u * r s = r s * u := by
    intro s hs
    have e1 := hH s hs
    have e2 := hH (t * s * t⁻¹) (by simp [hs])
    simp only [map_mul, map_inv] at e2
    rw [e1, hrt] at e2
    have e3 : u * r s = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u := by
      group
    rw [e3, e2]; group
  obtain ⟨c, hc⟩ := schur_scalar_of_commutes_irreducible (r.comp φ) hirr (u : Matrix (Fin n) (Fin n) k) (by
    intro x
    have := hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)
    simpa using congrArg Units.val this)
  have hcen : ∀ a : GL (Fin n) k, u * a = a * u := by
    intro a
    apply Units.ext
    simp [hc]
  have huu : u * u = 1 := by
    have e2 := hH (t * t) (by simp [ht'])
    simp only [map_mul] at e2
    rw [hrt] at e2
    have e3 : u * r t * u = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g := by group
    rw [e2, hcen (r t)] at e3
    calc u * u = (r t)⁻¹ * (r t * u * u) := by group
      _ = 1 := by rw [e3]; group
  have hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹ := by
    intro s hs
    have e1 := hH (t⁻¹ * s) (by simp [hs, ht'])
    have e2 : r' s = r' t * r' (t⁻¹ * s) := by rw [← map_mul]; simp
    rw [e2, e1, hrt, ← hcen (r t), map_mul, map_inv]; group
  have hu2 : u = 1 ∨ u = -1 := by
    have e := congrArg Units.val huu
    rw [Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one] at e
    have hn : Nonempty (Fin n) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hirr.1 (Subsingleton.elim _ _)
    obtain ⟨i⟩ := hn
    have e' := congrFun (congrFun e i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'
    rcases mul_self_eq_one_iff.1 e' with h | h
    · left; apply Units.ext; simp [hc, h]
    · right; apply Units.ext; simp [hc, h]
  rcases hu2 with h | h
  · refine Or.inl ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · exact hH s hs
    · rw [hneg s hs, h, one_mul]
  · refine Or.inr ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · rw [hH s hs]; congr 2; apply Units.ext; simp [tw_val, hs]
    · rw [hneg s hs, h]; congr 2; apply Units.ext; simp [tw_val, hs]

/- English proof (translation)
Use `⟨hirr.1, fun _ _ _ => trivial, ?_⟩` and prove the remaining obligations. Introduce `W _ hW`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨hW0, hW1⟩` from `hcon`.

Apply `hn` to reduce the goal to its premises. Distinguish the cases in `hall : ∀ s, δ s = 1`. Use `⟨1, fun s => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[tw_val, hall s]`.

Use `push Not at hall`. Take `⟨t, ht⟩` from `hall`. Establish `ht' : δ t = -1` using `(h2 t).resolve_left ht`. Set `ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k)` to `fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)`. Establish `hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v`.

Introduce `a b v`. Simplify using `[ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]`. Establish `a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W`. Introduce `s hs v hv`. Take `⟨x, rfl⟩` from `(h1 s).1 hs`.

Conclude with `hW x v hv`. Establish `a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t)`. Introduce `s hs v hv`. Use `⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩` and prove the remaining obligations. Rewrite using `[hmul]`.

Simplify using the standard rewrite rules. Establish `a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t)`. Introduce and unpack `s hs _ ⟨v, hv, rfl⟩`. Rewrite using `[hmul]; exact a2 _ (by simp [hs, ht']) v hv`. Establish `a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W`.

Introduce and unpack `s hs _ ⟨v, hv, rfl⟩`. Rewrite using `[hmul]; exact a1 _ (by simp [hs, ht']) v hv`. Establish `hinf : W ⊓ W.map (ρ t) = ⊥`. Use `(hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))` and prove the remaining obligations. Introduce `s v hv`.

Break down `h2 s with hs | hs` into its components or cases. Conclude with `⟨a1 s hs v hv.1, a3 s hs v hv.2⟩`. Conclude with `⟨a4 s hs v hv.2, a2 s hs v hv.1⟩`. Establish `hsup : W ⊔ W.map (ρ t) = ⊤`. Use `(hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))` and prove the remaining obligations.

Introduce `s v hv`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`. Use `show ρ s (a + b) ∈ _`. Rewrite using `[map_add]`. Break down `h2 s with hs | hs` into its components or cases.

Conclude with `Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)`. Rewrite using `[add_comm]`. Conclude with `Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)`. Establish `hc : IsCompl W (W.map (ρ t))` using `IsCompl.of_eq hinf hsup`. Set `P : (Fin n → k) →ₗ[k] (Fin n → k)` to `LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)`.

Establish `p1 : ∀ v ∈ W, P v = v` using `fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)`. Establish `p2 : ∀ v ∈ W.map (ρ t), P v = -v` using `fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)`. Establish `hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v` using `fun v => Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)`. Establish `hPP : P ∘ₗ P = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Take `⟨a, ha, b, hb, rfl⟩` from `hdec v`. Simplify using `[p1 a ha, p2 b hb]`. Establish `hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s`. Introduce `s`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Take `⟨a, ha, b, hb, rfl⟩` from `hdec v`. Break down `h2 s with hs | hs` into its components or cases. Simplify using `[p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]`. Simplify using `[p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]`. Establish `hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1`.

Rewrite using `[← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]`. Use `⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg LinearMap.toMatrix' (hPr s)` as an intermediate fact.

Simplify using `only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this`. Simplify using `only [Units.val_mul, tw_val, Matrix.smul_mul]`. Conclude with `this`.
-/
private theorem part_one {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (hn : ¬ RepIso r (tw r δ)) : IsIrr (r.comp φ) := by
  refine ⟨hirr.1, fun _ _ _ => trivial, ?_⟩
  intro W _ hW
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  apply hn
  by_cases hall : ∀ s, δ s = 1
  · refine ⟨1, fun s => ?_⟩
    apply Units.ext; simp [tw_val, hall s]
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)
  have hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v
    simp [ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  have a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W := by
    intro s hs v hv
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hW x v hv
  have a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t) := by
    intro s hs v hv
    refine ⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩
    rw [hmul]; simp
  have a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t) := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a2 _ (by simp [hs, ht']) v hv
  have a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a1 _ (by simp [hs, ht']) v hv
  have hinf : W ⊓ W.map (ρ t) = ⊥ := by
    refine (hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))
    intro s v hv
    rcases h2 s with hs | hs
    · exact ⟨a1 s hs v hv.1, a3 s hs v hv.2⟩
    · exact ⟨a4 s hs v hv.2, a2 s hs v hv.1⟩
  have hsup : W ⊔ W.map (ρ t) = ⊤ := by
    refine (hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))
    intro s v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show ρ s (a + b) ∈ _
    rw [map_add]
    rcases h2 s with hs | hs
    · exact Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)
    · rw [add_comm]; exact Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)
  have hc : IsCompl W (W.map (ρ t)) := IsCompl.of_eq hinf hsup
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)
  have p1 : ∀ v ∈ W, P v = v := fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)
  have p2 : ∀ v ∈ W.map (ρ t), P v = -v := fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)
  have hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v := fun v =>
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hPP : P ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    simp [p1 a ha, p2 b hb]
  have hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s := by
    intro s
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rcases h2 s with hs | hs
    · simp [p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]
    · simp [p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]
  have hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have := congrArg LinearMap.toMatrix' (hPr s)
  simp only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this
  simp only [Units.val_mul, tw_val, Matrix.smul_mul]
  exact this

/- English proof (translation)
Introduce `Γ Γ' k _ _ _ _ _ n φ δ h1 h2 r`. Conclude with `⟨part_one φ δ h1 h2 r, fun r' => part_two φ δ h1 h2 r r'⟩`.
-/
theorem UpperTheory.V.Br.resTwo :
    UpperTheory.V.Br.ResTwo := by
  intro Γ Γ' k _ _ _ _ _ n φ δ h1 h2 r
  exact ⟨part_one φ δ h1 h2 r, fun r' => part_two φ δ h1 h2 r r'⟩
