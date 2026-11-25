module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩

end GlobalTheory.Mem.Col2.TC
end
