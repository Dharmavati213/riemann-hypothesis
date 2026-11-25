module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra! hc
    apply h
    have hle : v.asIdeal ≤ (P.under (𝓞 D.host.F)).asIdeal := by
      intro x hx
      obtain ⟨y, hy, hyP⟩ := hc x hx
      have : y = algebraMap _ _ x := RingOfIntegers.ext hy
      subst this
      exact hyP
    have := v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top hle
    rwa [show P.under (𝓞 D.host.F) = v from HeightOneSpectrum.ext this.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

end
