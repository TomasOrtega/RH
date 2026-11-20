import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasA
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasB
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasC

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

/- English proof (translation)
Establish `hFe : ∀ n k, ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n` using `fun n k => filtX_e e X c h1 ρ ι hι n k`. Establish `hGF : ∀ x ∈ G, ∃ n, x ∈ filtX X ι n`. Introduce `x hx`. Establish `hdir : Directed (· ≤ ·) (filtX X ι)` using `(Monotone.directed_le fun _ _ h => filtX_mono X ι h)`. Establish `hle : G ≤ ⨆ n, filtX X ι n`.

Rewrite using `[hG]`. Use `sInf_le ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← filtX_zero X ι]`. Conclude with `le_iSup (filtX X ι) 0`. Introduce `k y hy`.

Take `⟨n, hn⟩` from `(Submodule.mem_iSup_of_directed _ hdir).1 hy`. Conclude with `Submodule.mem_iSup_of_mem n (hFe n k y hn)`. Introduce `i y hy`. Take `⟨n, hn⟩` from `(Submodule.mem_iSup_of_directed _ hdir).1 hy`. Conclude with `Submodule.mem_iSup_of_mem (n + 1) (filtX_X X ι n i y hn)`.

Conclude with `(Submodule.mem_iSup_of_directed _ hdir).1 (hle hx)`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `swap`. Take `⟨n, hn⟩` from `hGF x hx`. Conclude with `⟨filtX X ι n, filtX_fd X ι n, hn, hFe n⟩`.

Use `set C : Module.End ℂ M := (∑ k, e k * e (σ k)) - (c0 : ℂ) • (1 : Module.End ℂ M) with hC`. Establish `hCa : ∀ x, C x = (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x` using `fun x => by simp [hC]`. Establish `hCF : ∀ n, ∀ x ∈ filtX X ι n, C x ∈ filtX X ι n`. Introduce `n x hx`. Rewrite using `[hCa, LinearMap.sum_apply]`.

Conclude with `Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => hFe n k _ (hFe n _ x hx)) (Submodule.smul_mem _ _ hx)`. Establish `hsurj : ∀ n, filtX X ι (n + 1) ≤ filtX X ι n ⊔ (filtX X ι (n + 1)).map C`. Introduce `n`. Assume the negation of the conclusion as `hcon`. Take `⟨x, hx, hxn⟩` from `SetLike.not_le_iff_exists.1 hcon`.

Take `⟨φ, hφx, hφ0⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hxn inferInstance`. Establish `hφz : ∀ y ∈ filtX X ι n ⊔ (filtX X ι (n + 1)).map C, φ y = 0`. Introduce `y hy`. Establish `: φ y ∈ (filtX X ι n ⊔ (filtX X ι (n + 1)).map C).map φ` using `Submodule.mem_map_of_mem hy`. Rewrite `this` using `[hφ0]`.

Conclude with `(Submodule.mem_bot ℂ).1 this`. Set `W : (Fin (n + 1) → I) → Module.End ℂ M` to `fun w => wordX X (List.ofFn w)`. Establish `hex : ∀ w : Fin (n + 1) → I, ∃ u : V, ∀ v, ⟪u, v⟫_ℂ = φ (W w (ι v))`. Introduce `w`. Use `haveI : CompleteSpace V := FiniteDimensional.complete ℂ V`.

Use `⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap (φ ∘ₗ (W w) ∘ₗ ι)), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression. Use `choose Ψ hΨ using hex`. Establish `hWm : ∀ w v, W w (ι v) ∈ filtX X ι (n + 1)` using `fun w v => Submodule.subset_span ⟨List.ofFn w, v, by simp, rfl⟩`.

Establish `hΨ0 : Ψ = 0`. Use `cas_tensor σ hσ e c c0 h3 ρ hadj hc0 ι hι W (fun k w => wordX_comm e X c h1 k (n + 1) w) φ Ψ hΨ (fun w v => ?_) (fun s w => ?_)` and prove the remaining obligations. Rewrite using `[← hCa]`. Conclude with `hφz _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hWm w v)))`. Use `cas_one σ hσ e X c d c0 h1 h3 h4 ρ hadj hc0 ι hι h5 (fun i => Ψ (Function.update w s i)) (fun Θ hΘ => ?_)` and prove the remaining obligations.

Establish `key : ∀ i, ⟪Ψ (Function.update w s i), Θ i⟫_ℂ = φ (wordX X ((List.ofFn w).eraseIdx s) (X i (ι (Θ i))))`. Introduce `i`. Rewrite using `[hΨ]`. Establish `hp : (List.ofFn (Function.update w s i)).Perm ((List.ofFn w).eraseIdx s ++ [i])`. Establish `e1 : List.ofFn (Function.update w s i) = (List.ofFn w).set s i`.

Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `m h1 h2`. Rewrite using `[List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]`. Distinguish the cases in `hm : (s : ℕ) = m`.

Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hm, Function.update_of_ne]`. Introduce `h; exact hm (by rw [← h])`. Rewrite using `[e1]`.

Conclude with `(List.set_perm_cons_eraseIdx (by simpa using s.2) i).trans (List.perm_append_singleton _ _).symm`. Establish `hm` using `filtX_perm e X c h1 h2 ρ ι hι hp n (by simp) (Θ i)`. Establish `h0` using `hφz _ (Submodule.mem_sup_left hm)`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Use `h0.trans ?_` and prove the remaining obligations.

Simplify using `[wordX]`. Simplify using `only [key]`. Rewrite using `[← map_sum, ← map_sum, hΘ, map_zero, map_zero]`. Apply `hφx` to reduce the goal to its premises. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 (filtX_succ_le X ι n hx)`.

Rewrite using `[map_add, hφz y (Submodule.mem_sup_left hy), zero_add]`. Establish `: Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} ≤ LinearMap.ker φ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, v, rfl⟩`. Use `hΨ w v` as an intermediate fact.

Rewrite `this` using `[hΨ0]`. Rewrite `this` using `[Pi.zero_apply, inner_zero_left]`. Conclude with `this.symm`. Conclude with `this hz`. Establish `hstep : ∀ n, ∀ x ∈ filtX X ι (n + 1), C x ∈ filtX X ι n → x ∈ filtX X ι n`.

Introduce `n x hx hCx`. Use `haveI := filtX_fd X ι (n + 1)`. Set `P : Submodule ℂ (filtX X ι (n + 1))` to `(filtX X ι n).comap (filtX X ι (n + 1)).subtype`. Set `C1 : Module.End ℂ (filtX X ι (n + 1))` to `C.restrict (hCF (n + 1))`. Establish `hP : P ≤ P.comap C1` using `fun y hy => hCF n y hy`.

Establish `hs : Function.Surjective (P.mapQ P C1 hP)`. Introduce `z`. Take `⟨y, rfl⟩` from `P.mkQ_surjective z`. Take `⟨a, ha, _, ⟨b, hb, rfl⟩, hab⟩` from `Submodule.mem_sup.1 (hsurj n y.2)`. Use `⟨P.mkQ ⟨b, hb⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]`. Use `show C b - (y : M) ∈ filtX X ι n`. Rewrite using `[← hab]`. Simplify using `using ha`. Establish `hi : Function.Injective (P.mapQ P C1 hP)` using `LinearMap.injective_iff_surjective.2 hs`.

Establish `: P.mkQ ⟨x, hx⟩ = 0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hCx`. Conclude with `(Submodule.Quotient.mk_eq_zero P).1 this`.

Introduce `x hx hCx`. Rewrite `hCx` using `[← hCa, ← filtX_zero X ι]`. Rewrite using `[← filtX_zero X ι]`. Take `⟨n, hn⟩` from `hGF x hx`. Proceed by induction on `n with`.

Consider the case `zero => exact hn`. Consider the case `succ n ih => exact ih (hstep n x hn (filtX_mono X ι (Nat.zero_le n) hCx))`.
-/
theorem cas_bound {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e))
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (G : Submodule ℂ M)
    (hG : G = sInf {N | LinearMap.range ι ≤ N ∧ (∀ k, ∀ x ∈ N, e k x ∈ N) ∧ ∀ i, ∀ x ∈ N, X i x ∈ N}) :
    (∀ x ∈ G, (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ G, ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ ∀ k, ∀ y ∈ F, e k y ∈ F := by
  classical
  have hFe : ∀ n k, ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := fun n k => filtX_e e X c h1 ρ ι hι n k
  have hGF : ∀ x ∈ G, ∃ n, x ∈ filtX X ι n := by
    intro x hx
    have hdir : Directed (· ≤ ·) (filtX X ι) := (Monotone.directed_le fun _ _ h => filtX_mono X ι h)
    have hle : G ≤ ⨆ n, filtX X ι n := by
      rw [hG]
      refine sInf_le ⟨?_, ?_, ?_⟩
      · rw [← filtX_zero X ι]; exact le_iSup (filtX X ι) 0
      · intro k y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem n (hFe n k y hn)
      · intro i y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem (n + 1) (filtX_X X ι n i y hn)
    exact (Submodule.mem_iSup_of_directed _ hdir).1 (hle hx)
  refine ⟨?_, fun x hx => ?_⟩
  swap
  · obtain ⟨n, hn⟩ := hGF x hx
    exact ⟨filtX X ι n, filtX_fd X ι n, hn, hFe n⟩
  set C : Module.End ℂ M := (∑ k, e k * e (σ k)) - (c0 : ℂ) • (1 : Module.End ℂ M) with hC
  have hCa : ∀ x, C x = (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x := fun x => by simp [hC]
  have hCF : ∀ n, ∀ x ∈ filtX X ι n, C x ∈ filtX X ι n := by
    intro n x hx
    rw [hCa, LinearMap.sum_apply]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => hFe n k _ (hFe n _ x hx)) (Submodule.smul_mem _ _ hx)

  have hsurj : ∀ n, filtX X ι (n + 1) ≤ filtX X ι n ⊔ (filtX X ι (n + 1)).map C := by
    intro n
    by_contra hcon
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.1 hcon
    obtain ⟨φ, hφx, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxn inferInstance
    have hφz : ∀ y ∈ filtX X ι n ⊔ (filtX X ι (n + 1)).map C, φ y = 0 := by
      intro y hy
      have : φ y ∈ (filtX X ι n ⊔ (filtX X ι (n + 1)).map C).map φ := Submodule.mem_map_of_mem hy
      rw [hφ0] at this
      exact (Submodule.mem_bot ℂ).1 this
    let W : (Fin (n + 1) → I) → Module.End ℂ M := fun w => wordX X (List.ofFn w)
    have hex : ∀ w : Fin (n + 1) → I, ∃ u : V, ∀ v, ⟪u, v⟫_ℂ = φ (W w (ι v)) := by
      intro w
      haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
      refine ⟨(InnerProductSpace.toDual ℂ V).symm
        (LinearMap.toContinuousLinearMap (φ ∘ₗ (W w) ∘ₗ ι)), fun v => ?_⟩
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    choose Ψ hΨ using hex
    have hWm : ∀ w v, W w (ι v) ∈ filtX X ι (n + 1) := fun w v =>
      Submodule.subset_span ⟨List.ofFn w, v, by simp, rfl⟩
    have hΨ0 : Ψ = 0 := by
      refine cas_tensor σ hσ e c c0 h3 ρ hadj hc0 ι hι W (fun k w => wordX_comm e X c h1 k (n + 1) w) φ Ψ hΨ
        (fun w v => ?_) (fun s w => ?_)
      · rw [← hCa]
        exact hφz _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hWm w v)))
      · refine cas_one σ hσ e X c d c0 h1 h3 h4 ρ hadj hc0 ι hι h5 (fun i => Ψ (Function.update w s i))
          (fun Θ hΘ => ?_)
        have key : ∀ i, ⟪Ψ (Function.update w s i), Θ i⟫_ℂ =
            φ (wordX X ((List.ofFn w).eraseIdx s) (X i (ι (Θ i)))) := by
          intro i
          rw [hΨ]
          have hp : (List.ofFn (Function.update w s i)).Perm ((List.ofFn w).eraseIdx s ++ [i]) := by
            have e1 : List.ofFn (Function.update w s i) = (List.ofFn w).set s i := by
              apply List.ext_getElem
              · simp
              · intro m h1 h2
                rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
                by_cases hm : (s : ℕ) = m
                · subst hm; simp
                · rw [if_neg hm, Function.update_of_ne]
                  intro h; exact hm (by rw [← h])
            rw [e1]
            exact (List.set_perm_cons_eraseIdx (by simpa using s.2) i).trans
              (List.perm_append_singleton _ _).symm
          have hm := filtX_perm e X c h1 h2 ρ ι hι hp n (by simp) (Θ i)
          have h0 := hφz _ (Submodule.mem_sup_left hm)
          rw [map_sub, sub_eq_zero] at h0
          refine h0.trans ?_
          simp [wordX]
        simp only [key]
        rw [← map_sum, ← map_sum, hΘ, map_zero, map_zero]
    apply hφx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (filtX_succ_le X ι n hx)
    rw [map_add, hφz y (Submodule.mem_sup_left hy), zero_add]
    have : Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} ≤
        LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, v, rfl⟩
      have := hΨ w v
      rw [hΨ0] at this
      rw [Pi.zero_apply, inner_zero_left] at this
      exact this.symm
    exact this hz
  have hstep : ∀ n, ∀ x ∈ filtX X ι (n + 1), C x ∈ filtX X ι n → x ∈ filtX X ι n := by
    intro n x hx hCx
    haveI := filtX_fd X ι (n + 1)
    let P : Submodule ℂ (filtX X ι (n + 1)) := (filtX X ι n).comap (filtX X ι (n + 1)).subtype
    let C1 : Module.End ℂ (filtX X ι (n + 1)) := C.restrict (hCF (n + 1))
    have hP : P ≤ P.comap C1 := fun y hy => hCF n y hy
    have hs : Function.Surjective (P.mapQ P C1 hP) := by
      intro z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective z
      obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, hab⟩ := Submodule.mem_sup.1 (hsurj n y.2)
      refine ⟨P.mkQ ⟨b, hb⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
      show C b - (y : M) ∈ filtX X ι n
      rw [← hab]
      simpa using ha
    have hi : Function.Injective (P.mapQ P C1 hP) := LinearMap.injective_iff_surjective.2 hs
    have : P.mkQ ⟨x, hx⟩ = 0 := by
      apply hi
      rw [map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hCx
    exact (Submodule.Quotient.mk_eq_zero P).1 this
  intro x hx hCx
  rw [← hCa, ← filtX_zero X ι] at hCx
  rw [← filtX_zero X ι]
  obtain ⟨n, hn⟩ := hGF x hx
  induction n with
  | zero => exact hn
  | succ n ih => exact ih (hstep n x hn (filtX_mono X ι (Nat.zero_le n) hCx))

end PositivityTheory.KReal

end
