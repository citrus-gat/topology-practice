import tactic
import topology.basic

-- #check topological_space

/- From https://leanprover-community.github.io/theories/topology.html#filters: 
  given a map f from ℕ to a topological space X, one can check that the resulting
  sequence f 0, f 1, f 2... tends to x ∈ X if and only if the pre-image of any 
  element in the filter 𝓝 x is in the cofinite filter on ℕ -- this is just 
  another way of saying that given any open set U containing x, there exists N 
  such that for all n ≥ N, f n ∈ U. -/
example {X : Type*}[topological_space X]{f : ℕ → X}{x : X} : 
(∀ U : set X, is_open U ∧ x ∈ U → ∃ N : ℕ, ∀ n > N, f n ∈ U) ↔ 
(∀ S : set X, S ∈ nhds x → f⁻¹' S ∈ (@filter.cofinite ℕ) ) := 
begin 
  split,
  { -- Convergence implies preimage of neighborhood in the cofinite filter
    intros h S S_in,
    rw mem_nhds_iff at S_in,
    rcases S_in with ⟨U, U_ss_S, U_open, x_in_U⟩,
    rcases h U ⟨U_open, x_in_U⟩ with ⟨N, hN⟩, 
    rw filter.mem_cofinite,
    have : f⁻¹' U ⊆ f⁻¹'S := set.preimage_mono U_ss_S, 
    rw ← set.compl_subset_compl at this,
    suffices hs : (f⁻¹' U)ᶜ.finite, { exact set.finite.subset hs this, },
    -- Now we prove the complement of f⁻¹(U) is finite. The idea is that the 
    -- complement is contained in {1, ..., N} because for n > N, n ∈ f⁻¹(U). 
    -- So it must be finite. 
    have hc : (f⁻¹' U)ᶜ ⊆ {n : ℕ | n ≤ N}, 
    { rw set.compl_subset_comm,
      intros n n_in,
      have hn : n > N, { rw set.compl_set_of at n_in; exact lt_of_not_ge n_in },
      rw set.compl_set_of at n_in,
      exact hN n hn, },
    exact set.finite.subset (set.finite_le_nat N) hc, }, 
  { -- Preimage of neighborhood in cofinite filter implies conergence 
    rintros h U ⟨U_open, x_in_U⟩,
    have : U ∈ nhds x, { exact is_open.mem_nhds U_open x_in_U },
    specialize h U this,
    rw filter.mem_cofinite at h,
    -- Since (f ⁻¹' U)ᶜ ⊆ ℕ is finite, it is bounded above by some N ∈ ℕ.  
    have compl_bdd := bdd_above_def.1 (set.finite.bdd_above h), 
    cases compl_bdd with N hN,
    -- We claim that this N works. It is becaues for all n > N, n is not in the 
    -- complement of f⁻¹(U), so f(n) ∈ f⁻¹(U). 
    use N, 
    intros n hn,
    specialize hN n,
    have : n ∉ (f⁻¹' U)ᶜ := mt hN (by linarith [hn]),
    rwa set.not_mem_compl_iff at this },
end 

-- The principal filter is an ultrafilter 
-- https://leanprover-community.github.io/mathlib_docs/order/filter/basic.html#filter.principal_le_iff

-- If f : X → Y is continuous, ℱ is a filter of X, and ℱ → x ∈ X, then f_*(ℱ) → f(x) 
def filter_converge {X : Type*}[topological_space X](F : filter X)(x : X) := ∀ (U : set X), is_open U → x ∈ U → U ∈ F
#check filter_converge 

example {X Y: Type*}[topological_space X][topological_space Y]{F : filter X}{f : X → Y}{x : X} : 
continuous f → filter_converge F x → filter_converge (filter.map f F) (f x) := 
begin 
  intros fcts F_to_x fU fU_open fx_in_fU, 
  let U := f⁻¹' fU,
  have U_open : is_open U := is_open.preimage fcts fU_open, 
  have x_in_U : x ∈ U := fx_in_fU,
  have U_in_F : U ∈ F := F_to_x U U_open x_in_U,
  exact filter.mem_map.mpr U_in_F,
end 

-- If for every filter ℱ in X, ℱ → x ∈ X implies f_*(ℱ) → f(x), then f is continuous 
example {X Y : Type*}[topological_space X][topological_space Y]{f : X → Y} : 
(∀ (F : filter X) (x : X), filter_converge F x → filter_converge (filter.map f F) (f x)) 
→ (continuous f) := 
begin  
  -- sorry 
  have Nx_to_x : ∀ x : X, filter_converge (nhds x) x, 
  { intros x U U_open x_in_U, 
    exact is_open.mem_nhds U_open x_in_U },
  intros h, 
  rw continuous_iff_continuous_at, 
  intros x,
  rw continuous_at_def,
  intros A A_in_nhd,
  specialize h (nhds x) x (Nx_to_x x),
  rcases mem_nhds_iff.mp A_in_nhd with ⟨V, V_in, V_open, fx_in_V⟩,
  have V_in_pushforward : V ∈ filter.map f (nhds x) := h V V_open fx_in_V,
  have preimV_in_nhd : f⁻¹' V ∈ nhds x := by rwa filter.mem_map at V_in_pushforward, 
  rcases mem_nhds_iff.mp preimV_in_nhd with ⟨U, U_in, U_open, x_in_U⟩, 
  have : U ⊆ f⁻¹' A := subset_trans U_in (set.preimage_mono V_in),
  exact mem_nhds_iff.mpr ⟨U, this, U_open, x_in_U⟩,
end 

-- From the previous two examples, we conclude that f is continuous iff 
-- for all filter ℱ on X, ℱ → x implies f_*(ℱ) → f(x)
example {X Y : Type*}[topological_space X][topological_space Y]{f : X → Y} : 
continuous f ↔ (∀ (F : filter X) (x : X), filter_converge F x → filter_converge (filter.map f F) (f x)) :=
sorry 


-- It turns out ℱ → x is the same as filter.tendsto id ℱ (nhds x)
example {X : Type*}[topological_space X]{F : filter X}{x : X} :
filter_converge F x ↔ filter.tendsto id F (nhds x) := 
begin
  have filter_converge_iff_contain_nhds : filter_converge F x ↔ F ≤ (nhds x), -- ℱ ≤ 𝒩(x) means 𝒩(x) ⊆ ℱ
  { split, 
    { intros F_to_x N N_nhd, 
      rcases mem_nhds_iff.mp N_nhd with ⟨U, U_ss_N, U_open, x_in_U⟩, 
      have U_in_F : U ∈ F := F_to_x U U_open x_in_U, 
      exact filter.mem_of_superset U_in_F U_ss_N },
    { intros nhd_in_F U U_open x_in_U,
      have U_nhd : U ∈ (nhds x) :=  is_open.mem_nhds U_open x_in_U,
      exact nhd_in_F U_nhd } },
  rw filter_converge_iff_contain_nhds,
  unfold filter.tendsto,
  -- Since f is the identity, f⁻¹(S) = S for every S ⊆ X. So f_*(ℱ) = {S ⊆ X : f⁻¹(S) ∈ ℱ } = ℱ
  rwa filter.map_id,
end 

-- As a result of filter_converge_iff_contain_nhds, if 𝒩(x) is an ultrafilter, 
-- then it is the only filter that converges to x. 


-- If S ⊆ T, then 𝒫(S) ⊇ 𝒫(T). 
example {X : Type*}[topological_space X]{S T : set X} : S ⊆ T → filter.principal S ≤ filter.principal T := 
begin  
  intros S_ss_T F F_in_PT, -- want to show F ∈ 𝒫(S)
  have S_ss_F : S ⊆ F :=
    calc S ⊆ T : S_ss_T 
       ... ⊆ F : filter.mem_principal.mp F_in_PT,
  exact filter.mem_principal.mpr S_ss_F,
end 

-- Conversely, if 𝒫(S) ⊇ 𝒫(T) then S ⊆ T. 
example {X : Type*}[topological_space X]{S T : set X} : filter.principal S ≤ filter.principal T → S ⊆ T :=
begin 
  intro S_le_T,
  -- Since T ∈ 𝒫(T) ⊆ 𝒫(S), we have T ∈ 𝒫(S), and thus T ⊇ S
  have T_in_PT : T ∈ filter.principal T := filter.mem_principal_self T,
  have T_in_PS : T ∈ filter.principal S := filter.le_def.mp S_le_T T T_in_PT,
  exact filter.mem_principal.mp T_in_PS,
end 

-- And in mathlib this is filter.principal_mono
#check @filter.principal_mono


open filter 

-- f_*(𝒫(S)) = 𝒫(f(S))
example {X Y : Type*}[topological_space X][topological_space Y]{f : X → Y}{S : set X} : filter.map f (principal S) = principal (f '' S) := 
begin  
  -- simp, -- This alone will solve the goal, but let's work out the details 
  apply filter.ext,             -- We want to show for all set T, T ∈ f_*(𝒫(S)) ↔ T ∈ 𝒫(f(S))
  intro T,          
  rw [mem_map, mem_principal],  -- But T ∈ f_*(𝒫(S)) means f⁻¹(T) ∈ 𝒫(S) and f⁻¹(T) ⊇ S 
  rw ← set.image_subset_iff,    -- But f⁻¹(T) ⊇ S exactly when T ⊇ S
  rw ← mem_principal,    -- So we can conclude T ∈ 𝒫(S)
end 

-- In mathlib it is filter.map_principal
#check @filter.map_principal 