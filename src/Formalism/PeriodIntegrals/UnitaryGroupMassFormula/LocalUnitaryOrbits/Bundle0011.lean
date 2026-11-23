module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRes
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol Formalism.L2.SG.Sub NumberField IsDedekindDomain

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem redU_of_norm (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : RedU σ J ψ v Λ a Y :=
  redU_of σ J ψ v Λ (Orb.unitV_of σ J ψ v Λ hN hUN) hR a Y

theorem countU_of_res (hN : Orb.NormOne σ J ψ v) (hUN : Orb.UnitNorm σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ)
    (Y : TupV (E := E) v n a) : CountU σ J ψ v Λ a Y :=
  countU_of_bas' σ J ψ v Λ a Y (by
    classical
    intro hG
    obtain ⟨L, hLat, hL⟩ := hG.2.1
    subst Λ
    let M := latLoc (E := E) v (L : Set (Fin n → E))
    have hfg : M.FG := basLat_fg v L hLat
    have hspan : Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
      have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
      have hopen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hG.2.2.1 hfg
      rw [eq_top_iff]
      intro x _
      obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v
        (hopen.mem_nhds M.zero_mem) (fun _ : Unit => x)
      have hmem : t • x ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.subset_span (htx ())
      have hx : t⁻¹ • (t • x) ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
        Submodule.smul_mem _ t⁻¹ hmem
      rwa [inv_smul_smul₀ ht] at hx
    have : Submodule.IsFullLattice (Fv F v) M :=
      { toIsLattice := Submodule.IsLattice.of_fg (Fv F v) hfg, span_eq_top := hspan }
    have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 hfg
    have : Module.Free (v.adicCompletionIntegers F) M := Submodule.IsLattice.free (Fv F v) M
    let b := Module.finBasis (v.adicCompletionIntegers F) M
    let B := b.extendOfIsFullLattice (Fv F v)
    have hB (i) : B i = (b i : Fin n → Fv F v ⊗[F] E) :=
      Module.Basis.extendOfIsFullLattice_apply (Fv F v) b i
    have hmem (x : Fin n → Fv F v ⊗[F] E) : x ∈ M ↔
        ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
          x = ∑ i, (c i : Fv F v) • B i := by
      constructor
      · intro hx
        refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
        have h := congrArg (fun y : M => (y : Fin n → Fv F v ⊗[F] E)) (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm.trans (Finset.sum_congr rfl fun i _ => by rw [hB]; rfl)
      · rintro ⟨c, rfl⟩
        exact Submodule.sum_mem M fun i _ => by rw [hB]; exact M.smul_mem (c i) (b i).2
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h2 : Module.finrank F E = 2 := hG.1.1.2.2.1
    have hm : Module.finrank (v.adicCompletionIntegers F) M = 2 * n := by
      have h := Module.finrank_eq_card_basis B
      rw [Fintype.card_fin] at h
      rw [← h, Module.finrank_pi_fintype]
      simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [← hm]
    exact ⟨B, B.linearIndependent, hmem⟩) (resIdx_holds v)
    (redU_of_norm σ J ψ v Λ hN hUN hR a Y)

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaVCases
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev IE : Ideal (𝓞 E) := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))

abbrev QE : Type := 𝓞 E ⧸ IE (E := E) v

def sigO : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem sigO_coe (x : 𝓞 E) : (sigO σ x : E) = σ (x : E) := rfl

theorem sigO_alg (a : 𝓞 F) : sigO σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  rw [sigO_coe]
  show σ (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  exact σ.commutes _

theorem IE_le : IE (E := E) v ≤ (IE (E := E) v).comap (sigO σ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  have hc : (sigO σ).comp (algebraMap (𝓞 F) (𝓞 E)) = algebraMap (𝓞 F) (𝓞 E) := RingHom.ext (sigO_alg σ)
  rw [hc]

def sigQ : QE (E := E) v →+* QE (E := E) v := Ideal.quotientMap (IE (E := E) v) (sigO σ) (IE_le σ v)

theorem sigQ_mk (x : 𝓞 E) : sigQ σ v (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sigO σ x) := rfl

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x :=
  PI.OmLocU.Orb.sigma_invol σ h x

theorem sigQ_sigQ (h : IsCMExt F E σ) (x : QE (E := E) v) : sigQ σ v (sigQ σ v x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigQ_mk, sigQ_mk]
  congr 1
  apply RingOfIntegers.ext
  simp only [sigO_coe]
  exact sig_sig σ h _

theorem sigQ_alg (c : 𝓞 F ⧸ v.asIdeal) :
    sigQ σ v (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, sigQ_mk, sigO_alg]

def ResQ : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ ρ : OR (E := E) v →+* QE (E := E) v, IsRes σ v ϖ (sigQ σ v) ρ

def EtaLink : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (etaV (E := E) v = 1 ↔ ¬ (IE (E := E) v).IsPrime)

def QInert : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (IE (E := E) v).IsPrime → sigQ σ v ≠ RingHom.id _

def QSplit : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal), ∀ x, e (sigQ σ v x) = (e x).swap

theorem card_res : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_res : Finite (𝓞 F ⧸ v.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_res]
  exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem IE_ne_bot : IE (E := E) v ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot v.ne_bot

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdxPiWStd
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem latIdx (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem lamIdx (a : ℕ) (b : Fin (2 * n) → Fin n → Fv F v ⊗[F] E) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ latLoc (E := E) v Λ ↔
      ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (hR : ResIdx v) (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a) := by
  have hV := latIdx v Λ b hb hmem hR ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem basis_of (hCM : IsCMExt F E σ) (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      ∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem smul_tup {a : ℕ} (ϖ : Fv F v) (p : TupV (E := E) v n a) : ϖ • p = sc (E := E) v ϖ • p := by
  funext i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem idxPiW_std (a : ℕ) (hS : StdHyp σ J ψ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : IdxPiW v Λ a := by
  obtain ⟨L, hLat, rfl⟩ := hFull
  rintro _ _ ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := basis_of σ v hS.1 L hLat
  have e : smulSub ϖ (LW v (L : Set (Fin n → E)) a) = lamP v (L : Set (Fin n → E)) a ϖ := by
    ext X
    rw [mem_smulSub, lamP, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, by rw [DistribSMul.toAddMonoidHom_apply, smul_tup]⟩
  have e2 : LW v (L : Set (Fin n → E)) a = lamA v (L : Set (Fin n → E)) a := AddSubgroup.ext fun _ => Iff.rfl
  rw [e, e2, lamIdx v _ a b hb hmem (resIdx_holds v) ϖ hϖ, qv]
  push_cast
  ring

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitNormOfRes
section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
  PI.OmLocU.Red
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem tr_nd_field {k K : Type} [Field k] [Field K] [Algebra k K] (σ' : K ≃ₐ[k] K) (hne : σ' ≠ AlgEquiv.refl)
    (z : K) (hz : z ≠ 0) : ∃ t : K, t * z + σ' (t * z) ≠ 0 := by
  have hu : ∃ u : K, u + σ' u ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have h1 : (1 : K) + 1 = 0 := by simpa using h 1
    ext u
    have h2 : σ' u = -u := eq_neg_of_add_eq_zero_right (h u)
    rw [h2]
    show -u = u
    have h3 : u + u = 0 := by rw [← mul_one u, ← mul_add, h1, mul_zero]
    exact (eq_neg_of_add_eq_zero_left h3).symm
  obtain ⟨u, hu⟩ := hu
  refine ⟨u * z⁻¹, ?_⟩
  rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  exact hu

theorem tr_nd_prod {k : Type} [Field k] (z : k × k) (hz : z ≠ 0) :
    ∃ t : k × k, t * z + (RingEquiv.prodComm (R := k) (S := k)).toRingHom (t * z) ≠ 0 := by
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by
      intro h2
      exact hz (Prod.ext h1 h2)
    refine ⟨(0, z.2⁻¹), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h2] at this
  · refine ⟨(z.1⁻¹, 0), fun h => ?_⟩
    have := congrArg Prod.fst h
    simp [inv_mul_cancel₀ h1] at this

theorem trNd_of_res {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hcm : IsCMExt F E σ)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (hres : IsRes σ v ϖ τ π) (hnd : ∀ z : K, z ≠ 0 → ∃ t : K, t * z + τ (t * z) ≠ 0)
    (c : Fv F v ⊗[F] E) (hc : c ∈ OEv (E := E) v) (hcn : sc (E := E) v (ϖ⁻¹) * c ∉ OEv (E := E) v) :
    ∃ t ∈ OEv (E := E) v, IsU v (t * c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * c)) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨hsurj, hker, hsig⟩ := hres
  let cO : OR (E := E) v := ⟨c, hc⟩
  have hc0 : π cO ≠ 0 := by
    intro h
    obtain ⟨d, hd0, hd⟩ := (hker cO).1 h
    apply hcn
    have hd' : c = sc (E := E) v ϖ * d := hd
    rw [hd', ← mul_assoc, sc_eq, sc_eq, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul]
    exact hd0
  obtain ⟨tb, htb⟩ := hnd _ hc0
  obtain ⟨tO, htO⟩ := hsurj tb
  have ht0 : (tO : Fv F v ⊗[F] E) ∈ OEv (E := E) v := tO.2
  have htc0 : (tO : Fv F v ⊗[F] E) * c ∈ OEv (E := E) v := (tO * cO).2
  let yO : OR (E := E) v := ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c), sigR_mem σ v htc0⟩
  have hy : π yO = τ (π (tO * cO)) := hsig (tO * cO) yO rfl
  set s := (tO : Fv F v ⊗[F] E) * c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((tO : Fv F v ⊗[F] E) * c) with hs
  have hsO : π (tO * cO + yO) ≠ 0 := by
    rw [map_add (f := _), hy, map_mul, htO]
    exact htb
  have hs0 : s ∈ OEv (E := E) v := (tO * cO + yO).2
  have hsf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ s = s := by
    rw [hs, map_add (f := _), sigR_invol σ v hcm, add_comm]
  refine ⟨tO, ht0, ?_⟩
  obtain ⟨a, ha, hsa⟩ := fix_int σ v hcm hs0 hsf
  rw [← hs, hsa]
  by_cases hva : Valued.v a < 1
  · exfalso
    obtain ⟨d, hd⟩ := (mem_unifO_iff v hϖ ⟨a, ha⟩).2 hva
    apply hsO
    apply (hker _).2
    refine ⟨sc (E := E) v (d : Fv F v), sc_mem v d.2, ?_⟩
    show s = _
    rw [hsa, sc_eq, sc_eq, sc_eq, ← map_mul]
    exact congrArg _ hd
  · have ha1 : Valued.v a = 1 := le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 ha) (not_lt.1 hva)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha1
      exact zero_ne_one ha1
    have hai : a⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha1, inv_one]
    refine ⟨sc (E := E) v (a⁻¹), sc_mem v hai, ?_⟩
    rw [sc_eq, sc_eq, ← map_mul, mul_inv_cancel₀ ha0, map_one]

theorem trNd_of (hR : ResAlg σ J ψ v) : TrNd σ J ψ v := by
  intro hstd hun ϖ hϖ c hc hcn
  obtain ⟨k, _, _, -, hcase⟩ := hR hstd hun ϖ hϖ
  rcases hcase with ⟨-, K, _, _, σ', π, -, -, hne, hres⟩ | ⟨-, π, hres⟩
  · exact trNd_of_res σ v (σ' : K →+* K) π hstd.1 hϖ hres (fun z hz => tr_nd_field σ' hne z hz) c hc hcn
  · exact trNd_of_res σ v _ π hstd.1 hϖ hres (fun z hz => tr_nd_prod z hz) c hc hcn

theorem unitNorm_of_res (hR : ResAlg σ J ψ v) : UnitNorm σ J ψ v Λ :=
  unitNorm_of σ J ψ v Λ (fixLoc_holds σ v) (trNd_of σ J ψ v hR) (primPerp_holds σ J ψ v Λ)

end PI.OmLocU.UnN
end
end

