module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiProjectiveHarrisTaylorFamily
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem exists_repFam_qproj : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp
  obtain ⟨e, hep, he⟩ := D.perfP
  have hp := (Fact.out : p.Prime)
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [Nat.coprime_zero_left] at hep
      exact absurd hep hp.one_lt.ne'
    · exact h
  obtain ⟨M, hMge, hMp⟩ := Nat.exists_infinite_primes (p + e + 3)
  have hM3 : 3 ≤ M := by omega
  have hModd : Odd M := hMp.odd_of_ne_two (by omega)
  have hMcp : M.Coprime p := (Nat.coprime_primes hMp hp).2 (by omega)
  have hMe : M.Coprime e := (Nat.Prime.coprime_iff_not_dvd hMp).2 fun h => by
    have := Nat.le_of_dvd he0 h
    omega
  have hg : 1 ≤ Module.finrank ℤ D.La / 2 := by
    have := D.two_le_finrank_La
    omega
  exact GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
    (GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable p D R b N M e hN hNp hM3 hModd hMcp hep hMe he
      (GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime _ M e hg hM3 hModd he0 hMe))

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso
section
namespace GlobalTheory.TorKSField

theorem toroidalForFanKS : GlobalTheory.Published.ToroidalForFanKS :=
  _root_.GlobalTheory.RigChart.toroidalForFanKS_of_rigidForFan _root_.GlobalTheory.RigChart.rigidForFan_holds

end GlobalTheory.TorKSField
end

