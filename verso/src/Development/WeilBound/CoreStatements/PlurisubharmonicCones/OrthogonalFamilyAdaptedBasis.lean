import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

/- English proof (translation)
Use `letI : Module (𝓞 E) V := Module.compHom V ρ`. Establish `hρ : ∀ (a : 𝓞 E) (x : V), a • x = ρ a x` using `fun _ _ => rfl`. Set `N : Submodule (𝓞 E) V` to `Submodule.span (𝓞 E) (Set.range e)`. Set `N' : Submodule (𝓞 E) V` to `{ I.toAddSubmonoid with smul_mem' := fun a x hx => hst a x hx }`. Establish `hN : N.toAddSubgroup = I`.

Use `le_antisymm (fun x hx => ?_) ?_` and prove the remaining obligations. Establish `: N ≤ N'` using `Submodule.span_le.2 fun y hy => by`. Express the relevant statement in the definitionally equal form `y ∈ I`. Rewrite using `[← he]`. Conclude with `AddSubgroup.subset_closure hy`.

Conclude with `this hx`. Rewrite using `[← he, AddSubgroup.closure_le]`. Conclude with `Submodule.subset_span`. Use `haveI : Module.Finite (𝓞 E) N := Module.Finite.span_of_finite _ (Set.finite_range e)`. Take `⟨y, hy⟩` from `exists_linearIndependent_fin (K := E) (E := N)`.

Establish `hfin` using `finite_quotient_span hy (Fintype.card_fin _)`. Use `⟨_, fun i => (y i : V), fun i => ?_, fun a ha => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hN]`. Conclude with `(y i).2`. Use function extensionality and compare the values at `i`.

Use `Fintype.linearIndependent_iff.1 hy a (Subtype.ext ?_) i` and prove the remaining obligations. Simplify `ha` using `[hρ]`. Establish `h1 : oSpan ρ (fun i => (y i : V)) = ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup`. Use extensionality with `x`. Rewrite using `[TorPart.mem_oSpan_iff, Submodule.map_span, ← Set.range_comp, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun]`.

Conclude with `exists_congr fun c => eq_comm`. Establish `h2 : ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).comap N.subtype)` using `rfl`. Rewrite using `[h1, ← hN, h2, Submodule.comap_map_eq_of_injective N.injective_subtype]`. Conclude with `Nat.card_pos.ne'`.
-/
theorem exists_isOFamily {E L V : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    (ρ : 𝓞 E →+* Module.End L V) (I : AddSubgroup V) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) {n : ℕ} (e : Fin n → V)
    (he : AddSubgroup.closure (Set.range e) = I) : ∃ (r : ℕ) (v : Fin r → V), IsOFamily ρ I v := by
  letI : Module (𝓞 E) V := Module.compHom V ρ
  have hρ : ∀ (a : 𝓞 E) (x : V), a • x = ρ a x := fun _ _ => rfl
  let N : Submodule (𝓞 E) V := Submodule.span (𝓞 E) (Set.range e)
  let N' : Submodule (𝓞 E) V := { I.toAddSubmonoid with smul_mem' := fun a x hx => hst a x hx }
  have hN : N.toAddSubgroup = I := by
    refine le_antisymm (fun x hx => ?_) ?_
    · have : N ≤ N' := Submodule.span_le.2 fun y hy => by
        change y ∈ I
        rw [← he]
        exact AddSubgroup.subset_closure hy
      exact this hx
    · rw [← he, AddSubgroup.closure_le]
      exact Submodule.subset_span
  haveI : Module.Finite (𝓞 E) N := Module.Finite.span_of_finite _ (Set.finite_range e)
  obtain ⟨y, hy⟩ := exists_linearIndependent_fin (K := E) (E := N)
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨_, fun i => (y i : V), fun i => ?_, fun a ha => ?_, ?_⟩
  · rw [← hN]
    exact (y i).2
  · funext i
    refine Fintype.linearIndependent_iff.1 hy a (Subtype.ext ?_) i
    simpa [hρ] using ha
  · have h1 : oSpan ρ (fun i => (y i : V)) =
        ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup := by
      ext x
      rw [TorPart.mem_oSpan_iff, Submodule.map_span, ← Set.range_comp, Submodule.mem_toAddSubgroup,
        Submodule.mem_span_range_iff_exists_fun]
      exact exists_congr fun c => eq_comm
    have h2 : ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup.relIndex N.toAddSubgroup =
        Nat.card (N ⧸ ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).comap N.subtype) := rfl
    rw [h1, ← hN, h2, Submodule.comap_map_eq_of_injective N.injective_subtype]
    exact Nat.card_pos.ne'

/- English proof (translation)
Use `set W := Submodule.span L (Set.range w) with hW`. Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent' L (fun x : S => W.mkQ (x : V))`. Use `haveI : Finite κ := hli.finite`. Take `⟨k, ⟨e⟩⟩` from `Finite.exists_equiv_fin κ`. Use `⟨k, fun c => (a (e.symm c) : V), fun c => (a _).2, ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h1 : LinearIndependent L fun i => (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : W)` using `LinearIndependent.of_comp W.subtype hw`. Establish `h2` using `h1.sumElim_of_quotient (fun c => (a (e.symm c) : V)) (hli.comp e.symm e.symm.injective)`. Establish `h3` using `h2.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective`. Establish `h4 : Fin.append w (fun c => (a (e.symm c) : V)) = Sum.elim w (fun c => (a (e.symm c) : V)) ∘ finSumFinEquiv.symm`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp`. Rewrite using `[h4]`. Conclude with `h3`. Establish `h1 : W.mkQ x ∈ Submodule.span L (Set.range ((fun x : S => W.mkQ (x : V)) ∘ a))`. Rewrite using `[hsp]`.

Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`. Establish `h2 : Set.range ((fun x : S => W.mkQ (x : V)) ∘ a) = W.mkQ '' Set.range fun c => (a (e.symm c) : V)`. Rewrite using `[← Set.range_comp, ← e.symm.surjective.range_comp]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ]`.

Rewrite using `[range_append, Submodule.span_union]`. Conclude with `h1`.
-/
theorem exists_append {L V : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent L w) (S : Set V) :
    ∃ (k : ℕ) (q : Fin k → V), (∀ c, q c ∈ S) ∧ LinearIndependent L (Fin.append w q) ∧
      S ⊆ Submodule.span L (Set.range (Fin.append w q)) := by
  set W := Submodule.span L (Set.range w) with hW
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' L (fun x : S => W.mkQ (x : V))
  haveI : Finite κ := hli.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨k, fun c => (a (e.symm c) : V), fun c => (a _).2, ?_, fun x hx => ?_⟩
  · have h1 : LinearIndependent L fun i => (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : W) :=
      LinearIndependent.of_comp W.subtype hw
    have h2 := h1.sumElim_of_quotient (fun c => (a (e.symm c) : V)) (hli.comp e.symm e.symm.injective)
    have h3 := h2.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    have h4 : Fin.append w (fun c => (a (e.symm c) : V)) =
        Sum.elim w (fun c => (a (e.symm c) : V)) ∘ finSumFinEquiv.symm := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [h4]
    exact h3
  · have h1 : W.mkQ x ∈ Submodule.span L (Set.range ((fun x : S => W.mkQ (x : V)) ∘ a)) := by
      rw [hsp]
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h2 : Set.range ((fun x : S => W.mkQ (x : V)) ∘ a) = W.mkQ '' Set.range fun c => (a (e.symm c) : V) := by
      rw [← Set.range_comp, ← e.symm.surjective.range_comp]
      rfl
    rw [h2, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
    rw [range_append, Submodule.span_union]
    exact h1

/- English proof (translation)
Introduce `E L Ψ _ _ _ _ _ V _ _ _ _ A hΨ`. Use `⟨?_, fun r v hv s => ?_⟩` and prove the remaining obligations. Take `⟨n, e, -, he⟩` from `A.I_basis`. Conclude with `exists_isOFamily A.ρ A.I A.I_stable e he`. Use `haveI : Module.Finite L V := by`.

Take `⟨S, hS⟩` from `A.fg`. Use `⟨S, ?_⟩` and prove the remaining obligations. Rewrite using `[← A.span, ← hS, Submodule.span_span_of_tower]`. Take `⟨h1, h2, h3, h4⟩` from `tor_facts A hΨ hv s`. Take `⟨k, q, hq, hli, hsp⟩` from `exists_append h1 (A.eig s : Set V)`.

Establish `had : A.IsAdapted s v fun c => ⟨q c, (hq c).1⟩`. Use `⟨hli, le_antisymm ?_ fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[LinPt.fam, range_append, Submodule.span_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨c, rfl⟩)`. Conclude with `h2 a`.

Conclude with `(hq c).2`. Take `⟨c, hc, h5⟩` from `exists_smul_mem_eig A s hx`. Establish `hcL : algebraMap (𝓞 L) L c ≠ 0`. Rewrite using `[map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]`. Conclude with `hc`.

Establish `h6` using `hsp h5`. Rewrite `h6` using `[← algebraMap_smul L c]`. Conclude with `(Submodule.smul_mem_iff _ hcL).1 h6`. Take `⟨h5, h6⟩` from `sub_eig A had.2`. Establish `h7` using `relIndex_ne_zero had.1 h5 h6 h5`.

Rewrite `h7` using `[LinPt.fam, (index_split A had.1 h3 h4 hq).1]`. Establish `h8` using `linearIndependent_img A had.1 h4 hq`. Use `⟨k, _, hq, had, ?_, (rank_img A h8 hq (right_ne_zero_of_mul h7)).1, fun ι => ?_⟩` and prove the remaining obligations. Rewrite using `[← had.2, finrank_span_eq_card had.1, Fintype.card_fin]`. Rewrite using `[gramDet_eq]`.

Conclude with `gramDet_pos _ _ h8`.
-/
theorem orthogonal_family_adapted_basis : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A hΨ
  refine ⟨?_, fun r v hv s => ?_⟩
  · obtain ⟨n, e, -, he⟩ := A.I_basis
    exact exists_isOFamily A.ρ A.I A.I_stable e he
  haveI : Module.Finite L V := by
    obtain ⟨S, hS⟩ := A.fg
    refine ⟨S, ?_⟩
    rw [← A.span, ← hS, Submodule.span_span_of_tower]
  obtain ⟨h1, h2, h3, h4⟩ := tor_facts A hΨ hv s
  obtain ⟨k, q, hq, hli, hsp⟩ := exists_append h1 (A.eig s : Set V)
  have had : A.IsAdapted s v fun c => ⟨q c, (hq c).1⟩ := by
    refine ⟨hli, le_antisymm ?_ fun x hx => ?_⟩
    · rw [LinPt.fam, range_append, Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨c, rfl⟩)
      · exact h2 a
      · exact (hq c).2
    · obtain ⟨c, hc, h5⟩ := exists_smul_mem_eig A s hx
      have hcL : algebraMap (𝓞 L) L c ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
        exact hc
      have h6 := hsp h5
      rw [← algebraMap_smul L c] at h6
      exact (Submodule.smul_mem_iff _ hcL).1 h6
  obtain ⟨h5, h6⟩ := sub_eig A had.2
  have h7 := relIndex_ne_zero had.1 h5 h6 h5
  rw [LinPt.fam, (index_split A had.1 h3 h4 hq).1] at h7
  have h8 := linearIndependent_img A had.1 h4 hq
  refine ⟨k, _, hq, had, ?_, (rank_img A h8 hq (right_ne_zero_of_mul h7)).1, fun ι => ?_⟩
  · rw [← had.2, finrank_span_eq_card had.1, Fintype.card_fin]
  · rw [gramDet_eq]
    exact gramDet_pos _ _ h8

end LevelTowerAlt
