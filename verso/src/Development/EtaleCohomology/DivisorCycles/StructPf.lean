import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

/- English proof (translation)
Introduce `x hx`. Take `⟨g, -, rfl⟩` from `Submonoid.mem_map.mp hx`. Conclude with `h g`.
-/
theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

/- English proof (translation)
Introduce `Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots`. Establish `hdegL : ∀ Y ∈ lie ρ, Deg n Y` using `(hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2`. Establish `hinj : Function.Injective e` using `isLac_inj hLac`. Take `⟨p, hSys, hXeq, hadj⟩` from `hProj C N n X e hinj (hdegL X hX) hroots`. Establish `hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ` using `hTanLie C N (img ρ ⊤)`.

Establish `hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ` using `hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)`. Establish `hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i` using `fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by`. Rewrite using `[← hXeq]`. Conclude with `hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))`. Establish `hA` using `hAlg C N n p (lie ρ) hSys hbr hoff hdiag`.

Take `⟨hNormd, hKeeps⟩` from `hEnv Γ C N ρ`. Use `⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩, hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩` and prove the remaining obligations. Conclude with `Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)`.
-/
theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
