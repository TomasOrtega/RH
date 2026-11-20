import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

namespace GlobalTheory.InvSys

/- English proof (translation)
Establish `hx : x ∈ Submodule.span ℤ (Set.range b)` using `by rw [b.span_eq]; exact Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨i, rfl⟩ := hy`. Conclude with `hb i`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add y w _ _ hy hw`. Take `⟨z1, h1⟩` from `hy`. Take `⟨z2, h2⟩` from `hw`. Conclude with `⟨z1 + z2, by rw [map_add, h1, h2, smul_add]⟩`. Consider the case `smul a y _ hy`.

Take `⟨z, h⟩` from `hy`. Conclude with `⟨a • z, by rw [map_smul, h, smul_comm]⟩`.
-/
theorem exists_nsmul_of_basis {M κ : Type} [AddCommGroup M] (b : Module.Basis κ ℤ M) (f : M →ₗ[ℤ] M) (n : ℕ)
    (hb : ∀ i, ∃ z, f (b i) = n • z) (x : M) : ∃ z, f x = n • z := by
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hb i
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨z1, h1⟩ := hy; obtain ⟨z2, h2⟩ := hw
    exact ⟨z1 + z2, by rw [map_add, h1, h2, smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨z, h⟩ := hy
    exact ⟨a • z, by rw [map_smul, h, smul_comm]⟩

/- English proof (translation)
Introduce `p _ D g htow hsurj hinj`. Use `haveI := D.freeLa`. Set `b` to `Module.Free.chooseBasis ℤ D.La`. Use `choose y z hyz using hsurj`. Set `g' : ℕ → D.La →+ D.La` to `fun n => if h : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => y n h.1 h.2 (b i))).toAddMonoidHom else 0`.

Establish `sec : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z`. Introduce `n hn hc x`. Establish `hg' : g' n = (b.constr ℤ (fun i => y n hn hc (b i))).toAddMonoidHom`. Simplify using `only [g', dif_pos (And.intro hn hc)]`. Take `⟨w, hw⟩` from `exists_nsmul_of_basis b ((g n).toIntLinearMap ∘ₗ b.constr ℤ (fun i => y n hn hc (b i)) - LinearMap.id) n (fun i => ⟨z n hn hc (b i), by simp [Module.Basis.constr_basis, hyz]⟩) x`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hg']`. Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply] at hw`. Simplify using `only [LinearMap.toAddMonoidHom_coe]`. Rewrite using `[← hw]`.

Normalize the expressions using the abelian group laws. Use `⟨g', ?_, sec, ?_⟩` and prove the remaining obligations. Introduce `n m hn hm hc x`. Establish `hcn : n.Coprime p` using `Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hc`. Take `⟨z1, h1⟩` from `htow n m hn hm hc (g' (n * m) x)`.

Take `⟨z2, h2⟩` from `sec (n * m) (Nat.mul_pos hn hm) hc x`. Take `⟨z3, h3⟩` from `sec n hn hcn x`. Take `⟨w, hw⟩` from `hinj n hn hcn (g' (n * m) x - g' n x) (m • z2 - z1 - z3) (by`. Rewrite using `[map_sub, smul_sub, smul_sub]`. Rewrite `h1` using `[h2]`.

Establish `: g n (g' (n * m) x) = x + (n * m) • z2 - n • z1` using `by rw [h1]; abel`. Rewrite using `[this, h3]`. Rewrite using `[mul_smul]`. Use the proof step `abel)`. Conclude with `⟨w, by rw [← hw]; abel⟩`.

Introduce `n hn hc x`. Take `⟨z1, h1⟩` from `sec n hn hc (g n x)`. Take `⟨w, hw⟩` from `hinj n hn hc (g' n (g n x) - x) z1 (by rw [map_sub, h1]; abel)`. Conclude with `⟨w, by rw [← hw]; abel⟩`.
-/
theorem invSys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) → ∃ g' : ℕ → D.La →+ D.La, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := by
  intro p _ D g htow hsurj hinj
  haveI := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose y z hyz using hsurj
  let g' : ℕ → D.La →+ D.La := fun n =>
    if h : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => y n h.1 h.2 (b i))).toAddMonoidHom else 0
  have sec : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z := by
    intro n hn hc x
    have hg' : g' n = (b.constr ℤ (fun i => y n hn hc (b i))).toAddMonoidHom := by
      simp only [g', dif_pos (And.intro hn hc)]
    obtain ⟨w, hw⟩ := exists_nsmul_of_basis b
      ((g n).toIntLinearMap ∘ₗ b.constr ℤ (fun i => y n hn hc (b i)) - LinearMap.id) n
      (fun i => ⟨z n hn hc (b i), by simp [Module.Basis.constr_basis, hyz]⟩) x
    refine ⟨w, ?_⟩
    rw [hg']
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply] at hw
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [← hw]; abel
  refine ⟨g', ?_, sec, ?_⟩
  · intro n m hn hm hc x
    have hcn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hc
    obtain ⟨z1, h1⟩ := htow n m hn hm hc (g' (n * m) x)
    obtain ⟨z2, h2⟩ := sec (n * m) (Nat.mul_pos hn hm) hc x
    obtain ⟨z3, h3⟩ := sec n hn hcn x
    obtain ⟨w, hw⟩ := hinj n hn hcn (g' (n * m) x - g' n x) (m • z2 - z1 - z3) (by
      rw [map_sub, smul_sub, smul_sub]
      rw [h2] at h1
      have : g n (g' (n * m) x) = x + (n * m) • z2 - n • z1 := by rw [h1]; abel
      rw [this, h3]
      rw [mul_smul]; abel)
    exact ⟨w, by rw [← hw]; abel⟩
  · intro n hn hc x
    obtain ⟨z1, h1⟩ := sec n hn hc (g n x)
    obtain ⟨w, hw⟩ := hinj n hn hc (g' n (g n x) - x) z1 (by rw [map_sub, h1]; abel)
    exact ⟨w, by rw [← hw]; abel⟩

end GlobalTheory.InvSys
