
-- two-state 4-hop VI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
	ProcCount: 3;          -- number processors
	ValueCount:   3;       -- number of data values.
	RequestChannel:  0;                
	ForwardChannel:  1;
	ResponseChannel: 2;
	AckChannel:3;
	--VC3: 3;
	--QMax: 2;
	NumVCs: 4;
	NetMax: ProcCount*3;
	
	

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
	Proc: scalarset(ProcCount);   -- unordered range of processors
	Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
	Home: enum { HomeType };      -- need enumeration for IsMember calls
	Node: union { Home , Proc };
	AckCnt : 0..ProcCount-1;
	VCType: 0..NumVCs-1;

	/*MessageType: enum {  ReadReq,         -- request for data / exclusivity
											 ReadAck,         -- read ack (w/ data)
																						 
											 WBReq,           -- writeback request (w/ data)
											 WBAck,           -- writeback ack 
													 
											 RecallReq 				-- Request & invalidate a valid copy
										};*/
	MessageType: enum { GetSReq,
						GetMReq,
						FwdReadReq,
						FwdStoreReq,
						InvReq,
						InvAck,
						PutSReq,
						PutMReq,
						PutEReq,
						PutAck,
						data,
						data_ex,
						dataAck
	};

	Message:
		Record -- is like struct
			mtype: MessageType;
			src: Node;
			-- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
			dst: Node; 
			vc: VCType;
			val: Value;
			ackCnt: AckCnt;
            fwdTo: Node; -- to whom to forward to
		End;

	HomeState:
		Record
			state: enum { 	H_Shared,             --stable states
							H_Invalid, 
							H_Modified, 
							H_Exclusive,					
							H_MS_D,                 --transient states 
							H_IS_Da,
							H_IM_Da,
							H_SS_Da,
							H_SM_Da,
							H_MM_Da,
							H_MS_D_Da,
							H_IE_Da
						}; 								
			owner: Node;	
			sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
			val: Value; 
		End;

	ProcState:
		Record
			state: enum { 	P_Shared, P_Invalid, P_Modified,P_Exclusive,  -- stable states
							P_IS_D, P_IM_IaD, P_IM_Ia,  -- the rest are transient states
							P_SM_IaD, P_SM_Ia,
							P_MI_Pa, P_SI_Pa, P_II_Pa,P_II_Da_Pa,
							P_MI_Da,P_SI_Da_pa, -- for fwdgetX
							P_MS_Da, P_II_Ia, P_EI_Pa
									};
			val: Value;
			ackRecieved: AckCnt;
			ackRequired:AckCnt;
		End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
	HomeNode:  HomeState;
	Procs: array [Proc] of ProcState;
	Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
	InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
	msg_processed: boolean;
	LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
				 dst:Node;
				 src:Node;
				 vc:VCType;
				 val:Value; -- here is the data 
				 ack:AckCnt;
				 fwd_to: Node;
				 );
var msg:Message;
Begin

	Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
	msg.mtype := mtype;
	msg.src   := src;
	msg.vc    := vc;
	msg.val   := val;
	msg.dst   := dst;
	msg.fwdTo := fwd_to;
	msg.ackCnt:= ack;
	MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
	error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
	error "Unhandled state!";
End;


-- These arent needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
	if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
	then
		MultiSetAdd(n, HomeNode.sharers);
	endif;
End;



Function IsSharer(n:Node) : Boolean;
Begin
	return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;



Procedure RemoveFromSharersList(n:Node);
Begin
	MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;



Function ClearSharerList(): Boolean;
Begin
	MultiSetRemovePred(i:HomeNode.sharers, true);
	if MultiSetCount(i:HomeNode.sharers,true) = 0
	then 
		return true;
	else
		return false;
	endif;
End;



-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
	for n:Node do
		if (IsMember(n, Proc) &
				MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
		then
			if n != rqst
			then 
				-- Send invalidation message here 
				Send(InvReq, n, rqst, ForwardChannel, UNDEFINED, 0, UNDEFINED);
			endif;
		endif;
	endfor;
End;





Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
 

	-- The line below is not needed in Valid/Invalid protocol.  However, the 
	-- compiler barfs if we put this inside a switch, so it is useful to
	-- pre-calculate the sharer count here
	cnt := MultiSetCount(i:HomeNode.sharers, true);


	-- default to 'processing' message.  set to false otherwise
	msg_processed := true;

	switch HomeNode.state

	-------------------------------------------------------------------------------------
	-- stable states
	-------------------------------------------------------------------------------------

		-- Invalid state for Home DIR
		case H_Invalid: 

			switch msg.mtype

				-- If it is read request ie [GetS]
				case GetSReq: -- send data to req, add req to sharer, go to shared state
					if isundefined(HomeNode.owner) & cnt = 0 then
						Send(data_ex, msg.src, HomeType, ResponseChannel, HomeNode.val, 0, UNDEFINED);
						HomeNode.state := H_IE_Da;
						HomeNode.owner := msg.src;
					else
						Send(data, msg.src, HomeType, ResponseChannel, HomeNode.val, 0, UNDEFINED);
						HomeNode.state := H_IS_Da;
						AddToSharersList(msg.src) ;
					endif;

				-- If it is GetM
				case GetMReq: -- send data to req, set owner to req and change sate to modified
					-- check if the Dir is the owner
					--assert (msg.src = HomeNode.owner) "Writeback from non-owner";
					HomeNode.state := H_IM_Da;
					HomeNode.owner := msg.src;
					Send(data, msg.src, HomeType, ResponseChannel, HomeNode.val, 0, UNDEFINED);
                    
					

				-- PutS last
				case PutSReq: -- send put ack to req
					
					HomeNode.state := H_Invalid;
					Send(PutAck,msg.src, HomeType,ResponseChannel,UNDEFINED, 0, UNDEFINED);

				-- PUTM from non-owner
				case PutMReq:
					assert (msg.src != HomeNode.owner) "PutM from owner not allowed";
                    if (msg.src != HomeNode.owner)
                    then
                        HomeNode.state := H_Invalid;
                        Send(PutAck,msg.src, HomeType,ResponseChannel,UNDEFINED,0,UNDEFINED);
                    endif;
				case PutEReq:
					HomeNode.state := H_Invalid;
					Send(PutAck,msg.src, HomeType,ResponseChannel,UNDEFINED, 0, UNDEFINED);

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;


		
		case H_Shared:

			switch msg.mtype
				case GetSReq:  
					HomeNode.state :=H_SS_Da;
					AddToSharersList(msg.src) ;   
					Send(data, msg.src, HomeType, ResponseChannel, HomeNode.val,0,UNDEFINED);
					
								
				
				-- send data to req, send inv to sharers,
				-- clear sharer set owner to req and transition to modified
				case GetMReq: 
					--assert (msg.src = HomeNode.owner) "Writeback from non-owner";
					HomeNode.state := H_SM_Da;
					if IsSharer(msg.src) then
						Send(data, msg.src, HomeType, ResponseChannel, msg.val, cnt-1,UNDEFINED);
						
					else
						Send(data, msg.src, HomeType, ResponseChannel, msg.val, cnt,UNDEFINED);
					endif;
					 
					
					SendInvReqToSharers(msg.src);
					undefine HomeNode.sharers;
					HomeNode.owner := msg.src;
					

				-- remove req from sharers list and send put ack to req,
				-- move to invalid state absed on if it is the last req
				case PutSReq:

					RemoveFromSharersList(msg.src);
					Send(PutAck, msg.src, HomeType, ResponseChannel, UNDEFINED,0,UNDEFINED);
					if IsSharer(msg.src) then
						if cnt = 1 then
							HomeNode.state := H_Invalid; 
						else
							HomeNode.state := H_Shared;
						endif;
					endif;
					
					

				-- put data from non owner
				case PutMReq :
					--Assert(HomeNode.owner != msg.src) "It is shared and this shouldn't happen";
					if msg.src != HomeNode.owner then
						RemoveFromSharersList(msg.src);
						Send(PutAck, msg.src, HomeType, ResponseChannel, UNDEFINED,0,UNDEFINED);
					endif;
				case PutEReq:
					--HomeNode.state := H_Invalid;
					if msg.src != HomeNode.owner then
						Send(PutAck,msg.src, HomeType,ResponseChannel,UNDEFINED, 0, UNDEFINED);
						RemoveFromSharersList(msg.src);
					endif;
				case dataAck:
					HomeNode.state := H_Shared;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;


		case H_Modified:
			assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
			switch msg.mtype


				-- send fwd-gets to owner, add  the requester and 
				-- owner to shares and clear ownership and go to S_D state
				case GetSReq:
					
					HomeNode.state := H_MS_D_Da;
					
					AddToSharersList(msg.src) ;  
					AddToSharersList(HomeNode.owner) ;
					Send(FwdReadReq,HomeNode.owner,HomeType,ForwardChannel,UNDEFINED,0,msg.src);
					
					undefine HomeNode.owner; 
				

				-- send fwd-getm to owner and set owner to requester
				case GetMReq:
					HomeNode.state := H_MM_Da;
					
					
					Send(FwdStoreReq,HomeNode.owner,HomeType,ForwardChannel, UNDEFINED,0,msg.src);
					--again we need to check for ack before setting the owner, perhaps it can be another state
					HomeNode.owner := msg.src;

				-- send put ack to requester
				case PutSReq:
				 
					Send(PutAck,msg.src,HomeType,ResponseChannel, UNDEFINED,0,UNDEFINED);

				-- copy data to memeory if the data is coming from owner, clear owner and move to invalid state
				-- for either case send put ack to th requester
				case PutMReq:
					Send(PutAck, msg.src,HomeType, ResponseChannel,UNDEFINED,0, UNDEFINED);
					if (HomeNode.owner = msg.src) then
						-- copy data to memeory, how idk
						HomeNode.val := msg.val;
						LastWrite := HomeNode.val;
						undefine HomeNode.owner;
						HomeNode.state := H_Invalid;
					else
						HomeNode.state := H_Modified;
					endif;
				case PutEReq:

				else
					ErrorUnhandledMsg(msg, HomeType);
				
			endswitch;
		case H_Exclusive:
			switch msg.mtype
				case GetSReq:
					HomeNode.state := H_MS_D_Da;
					Send(FwdReadReq,  HomeNode.owner, HomeType, ForwardChannel, UNDEFINED,0,msg.src);
					AddToSharersList(msg.src);
					AddToSharersList(HomeNode.owner);
					undefine HomeNode.owner;
				case GetMReq:
					HomeNode.state := H_MM_Da;
					Send(FwdStoreReq, HomeNode.owner, HomeType, ForwardChannel,UNDEFINED,0,msg.src );
					HomeNode.owner := msg.src;
				case PutSReq:
					Send(PutAck, msg.src,HomeType,ResponseChannel, UNDEFINED,0,UNDEFINED);
				case PutMReq:
					Send(PutAck, msg.src,HomeType, ResponseChannel,UNDEFINED,0, UNDEFINED);
					if (HomeNode.owner = msg.src) then
						-- copy data to memeory, how idk
						HomeNode.val := msg.val;
						LastWrite := HomeNode.val;
						undefine HomeNode.owner;
						HomeNode.state := H_Invalid;
					else
						HomeNode.state := H_Modified;
					endif;
				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;

	-------------------------------------------------------------------------------------
	-- transient states
	-------------------------------------------------------------------------------------
		case H_IE_Da:
			switch msg.mtype
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					msg_processed := false; -- stall message in InBox
				case PutEReq:	
					msg_processed := false; -- stall message in InBox
				case dataAck:
					HomeNode.state := H_Exclusive;
				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;
		case H_MS_D_Da:
			switch msg.mtype
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					
					msg_processed := false; -- stall message in InBox
				case data:
					msg_processed := false; -- stall message in InBox

				case dataAck:
					HomeNode.state := H_MS_D;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;
			 
		case H_MM_Da:
			switch msg.mtype
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					msg_processed := false; -- stall message in InBox
			
				case dataAck:
					HomeNode.state := H_Modified;

				else
					ErrorUnhandledMsg(msg, HomeType); 
				endswitch;
		case H_SS_Da:
			switch msg.mtype
			
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					--assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
					msg_processed := false; -- stall message in InBox
			
				case dataAck:
					HomeNode.state := H_Shared;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;
		case H_MS_D:

			--GetS leads to stall
			switch msg.mtype
				case GetSReq:
					msg_processed := false; -- stall message in InBox

				-- GetM Too
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				-- remove requester form sharer and send put ack 
				case PutSReq:
					Send(PutAck, msg.src, HomeType, ResponseChannel,UNDEFINED,0,UNDEFINED);
					RemoveFromSharersList(msg.src);

				-- remove req from sharer list n send put ack
				case PutMReq:
					Send(PutAck, msg.src, HomeType, ResponseChannel,UNDEFINED,0,UNDEFINED);
					RemoveFromSharersList(msg.src);

				-- handle case where data is sent
			

				case data:
					--msg_processed := false; -- stall message in InBox
					
					HomeNode.val := msg.val;
					LastWrite := HomeNode.val;
					if cnt = 0 then
						HomeNode.state := H_Invalid;
					else
						HomeNode.state := H_Shared;
					endif;
				
				else
						ErrorUnhandledMsg(msg, HomeType);

			endswitch;
		case H_IS_Da:

			switch msg.mtype
			
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					msg_processed := false; -- stall message in InBox
			

				case dataAck:
					HomeNode.state := H_Shared;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;
		
		case H_IM_Da:
			switch msg.mtype
			
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					msg_processed := false; -- stall message in InBox
			
				

				case dataAck:
					HomeNode.state := H_Modified;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;

		case H_SM_Da:
			switch msg.mtype
			
				case GetSReq:
					msg_processed := false; -- stall message in InBox
				
				case GetMReq:
					msg_processed := false; -- stall message in InBox

				case PutSReq:
					msg_processed := false; -- stall message in InBox

				case PutMReq:
					msg_processed := false; -- stall message in InBox
			
				
				case dataAck:
					HomeNode.state := H_Modified;

				else
					ErrorUnhandledMsg(msg, HomeType);

			endswitch;
		else
			ErrorUnhandledState();

	endswitch;
		
End;


Procedure ProcReceive(msg:Message; p:Proc);
Begin


	-- default to 'processing' message.  set to false otherwise
	msg_processed := true;

	alias ps:Procs[p].state do
	alias pv:Procs[p].val do
	alias ack_rec:Procs[p].ackRecieved do
	alias ack_req:Procs[p].ackRequired do
	

switch ps
	-------------------------------------------------------------------------------------
	-- stable states
	-------------------------------------------------------------------------------------
	case P_Invalid:
		/*switch msg.mtype
		  case InvReq:
			undefine pv;
			ps := P_Invalid;
			Send(InvAck, msg.src, p, ResponseChannel,UNDEFINED,0, UNDEFINED);
		else
		  ErrorUnhandledMsg(msg, p);
		endswitch;*/ 
		-- nothing

	case P_Shared:

		switch msg.mtype

			-- Inv
			case InvReq:
				undefine pv;
				ps := P_Invalid;
				Send(InvAck, msg.src, p, ResponseChannel,UNDEFINED,0, UNDEFINED);
			case PutAck:
				undefine pv;
				ps := P_Invalid;
			else
				ErrorUnhandledMsg(msg, p);
		endswitch;


	case P_Modified:

		switch msg.mtype

			-- send data to requester and also director and go to shared state
			case FwdReadReq:
				Send(data, msg.fwdTo, p, ResponseChannel,pv, 0, UNDEFINED);
				Send(data, HomeType, p, ResponseChannel,pv, 0, UNDEFINED);
				ps := P_MS_Da;
			
			-- send data to requester and fo to invalid state
			case FwdStoreReq:
				Send(data, msg.fwdTo,p, ResponseChannel,pv,0, UNDEFINED);
				undefine pv;
				ps := P_MI_Da;
			
			else
				ErrorUnhandledMsg(msg, p);
		endswitch; 
	case P_Exclusive:
		switch msg.mtype
			case FwdReadReq:
				Send(data, msg.fwdTo, p, ResponseChannel,pv, 0, UNDEFINED);
				Send(data, HomeType, p, ResponseChannel,pv, 0, UNDEFINED);
				ps := P_MS_Da;
			
			-- send data to requester and fo to invalid state
			case FwdStoreReq:
				Send(data, msg.fwdTo,p, ResponseChannel,pv,0, UNDEFINED);
				undefine pv;
				ps := P_MI_Da;
			
			else
				ErrorUnhandledMsg(msg, p);
		endswitch; 


	-------------------------------------------------------------------------------------
	-- transient states
	-------------------------------------------------------------------------------------
	case P_MS_Da:
		switch msg.mtype
			case InvReq:
				msg_processed := false;
			case PutAck:
				msg_processed := false;
			case dataAck:
				ps := P_Shared;
			else
				ErrorUnhandledMsg(msg, p);
			endswitch;
	case P_IS_D:
		switch msg.mtype
			-- Inv-> stall
			case InvReq:
				 msg_processed := false;
			
			case data:
				if (msg.src = HomeType) then
					
					if (msg.ackCnt = 0 )then
						Send(dataAck,HomeType , p, AckChannel,UNDEFINED,0,UNDEFINED);
						ps := P_Shared;
						pv := msg.val;
					endif;
			
				else
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED); 
					Send(dataAck,msg.src, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ps := P_Shared;
					pv := msg.val;
					ack_rec :=0;
				endif;
			case data_ex:
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED); 
					ps := P_Exclusive;
			else
				ErrorUnhandledMsg(msg, p);
		endswitch


	case P_IM_IaD:

		switch msg.mtype
		
			-- stall
			case FwdReadReq:
				msg_processed := false;

			-- stall 
			case FwdStoreReq:
				msg_processed := false;

			-- if data from dir go to modified state but check for ack
			case data:
			pv := msg.val;
				if (msg.src = HomeType) then
					--Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					if (msg.ackCnt = 0 )then
						Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
						ps := P_Modified;
					else
						if msg.ackCnt = ack_rec then
						Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
							ack_req :=0;
							ack_rec :=0;
							ps := P_Modified;
						else
							ps := P_IM_Ia;
							ack_req := msg.ackCnt;
						endif;
					endif;
				else
					Send(dataAck,msg.src, p, AckChannel,UNDEFINED,0,UNDEFINED);
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ps := P_Modified;
					ack_rec :=0;
					ack_req :=0;

				endif;
				
			
			-- just send data back
			case InvAck:
				ack_rec := ack_rec + 1;

			else
				ErrorUnhandledMsg(msg, p);
		endswitch


	case P_IM_Ia:

		switch msg.mtype

			-- stall
			case FwdReadReq:
				msg_processed := false;

			-- stall 
			case FwdStoreReq:
				msg_processed := false;
			
		
			case InvAck:
				ack_rec := ack_rec+1;
				if (ack_rec = ack_req) then -- means the last inv-ack
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ps := P_Modified;
					ack_req := 0;
					ack_rec:=0;
				endif;
			else
				ErrorUnhandledMsg(msg, p);
		endswitch
		

	case P_SM_IaD:

		switch msg.mtype

			-- stall
			case FwdReadReq:
				msg_processed := false;

			-- stall 
			case FwdStoreReq:
				msg_processed := false;

			-- Inv
			case InvReq:
				undefine pv;
				ps := P_IM_IaD;
				Send(InvAck, msg.src, p, ResponseChannel, UNDEFINED,0,UNDEFINED);

			-- if data from dir go to modified state but check for ack
			case data:
				if (msg.src = HomeType) then
					--Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					if (msg.ackCnt = 0 )then
						Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
						ps := P_Modified;
					else
						if msg.ackCnt = ack_rec then
						Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
							ack_req :=0;
							ack_rec :=0;
							ps := P_Modified;
						else
							ps := P_SM_Ia;
							ack_req := msg.ackCnt;
						endif;
					endif;
				else
					Send(dataAck,msg.src, p, AckChannel,UNDEFINED,0,UNDEFINED);
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ps := P_Modified;
					ack_rec :=0;
					ack_req :=0;

				endif;
				/*if (msg.src = HomeType & msg.ackCnt = 0) then
					ps := P_Modified;
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
				endif ;
				if(msg.src = HomeType & msg.ackCnt>0) then
					ps := P_SM_Ia;
					ack_req := msg.ackCnt;
				endif;
				if(msg.src != HomeType) then
					ps := P_Modified;
					Send(dataAck,msg.src, p, AckChannel,UNDEFINED,0,UNDEFINED);
					Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ack_rec:=0;
					ack_req:=0;
				endif;
				pv := msg.val;*/
			 -- just send data back
			case InvAck:
				ack_rec := ack_rec + 1;
				
			else
				ErrorUnhandledMsg(msg, p);
		endswitch
	case P_SM_Ia:

		switch msg.mtype

			-- stall
			case FwdReadReq:
				msg_processed := false;

			-- stall 
			case FwdStoreReq:
				msg_processed := false;
			
			case InvAck:
				ack_rec := ack_rec+1;
				if (ack_rec = ack_req) then -- means the last inv-ack
				Send(dataAck,HomeType, p, AckChannel,UNDEFINED,0,UNDEFINED);
					ps := P_Modified;
					ack_req := 0;
					ack_rec :=0;
				endif;
			else
				ErrorUnhandledMsg(msg, p);
		endswitch

	case P_MI_Pa:

		switch msg.mtype

			-- send data to requester and dir and go to SI_A state
			case FwdReadReq:
				Send(data, msg.fwdTo, p, ResponseChannel,pv, 0, UNDEFINED);
				Send(data, HomeType, p, ResponseChannel,pv, 0, UNDEFINED);
				ps := P_SI_Da_pa;
		
			-- send data to requester and fo to II_A state
			case FwdStoreReq:
				Send(data, msg.fwdTo, p, ResponseChannel,pv, 0, UNDEFINED);
				ps := P_II_Da_Pa;

			-- go to invalid state
			case PutAck:
				undefine pv;
				ps := P_Invalid;
				--msg_processed :=false;

			else
				ErrorUnhandledMsg(msg, p);
		endswitch; 
	case P_SI_Da_pa:
		switch msg.mtype
			case InvReq:
				msg_processed := false;
			case PutAck:
				msg_processed := false;
			case dataAck:
				ps:=P_SI_Pa;
			else 
				ErrorUnhandledMsg(msg, p);
		endswitch;
	case P_MI_Da:
		switch msg.mtype
			case PutAck:
				msg_processed := false;
			case dataAck:
				ps:= P_Invalid;
			else
				ErrorUnhandledMsg(msg, p);
		endswitch; 
	case P_II_Da_Pa:
		switch msg.mtype
			case PutAck:
				msg_processed := false;
			case dataAck:
				ps := P_II_Pa;

			else
		endswitch;
	case P_SI_Pa:
		switch msg.mtype
			
			case InvReq:
				Send(InvAck,msg.src,p, ResponseChannel, UNDEFINED, 0, UNDEFINED);
				ps := P_II_Pa;
			
			case PutAck:
				undefine pv;
			 	ps := P_Invalid;

			else
				ErrorUnhandledMsg(msg, p);
		endswitch; 
	case P_II_Ia: 
		switch msg.mtype
			case InvReq:
				Send(InvAck,msg.src,p, ResponseChannel, UNDEFINED, 0, UNDEFINED);
				ps := P_Invalid;
			else

				ErrorUnhandledMsg(msg,p);
		endswitch;

	case P_II_Pa:
		switch msg.mtype
			case PutAck:
				undefine pv;
				ps := P_Invalid;
			
			else
				ErrorUnhandledMsg(msg, p);
			endswitch;

	----------------------------
	-- Error catch
	----------------------------
	else
		ErrorUnhandledState();

	endswitch;
	
	endalias;
	endalias;
	endalias;
	endalias;
End;


----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
-- these actions are load, store and evict (replacement)
ruleset n:Proc Do
	alias p:Procs[n] Do

	ruleset v:Value Do
		rule "Proc-Invalid state, store value"
	 	 (p.state = P_Invalid)
			==>
 			 --p.val := v;    
			  
			 Send(GetMReq, HomeType, n ,RequestChannel, UNDEFINED,UNDEFINED,UNDEFINED); -- changed value v to undefined
			 p.state := P_IM_IaD; 
			 
 			 --LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
		endrule;
	endruleset;

	rule "Proc-Invalid, Load req"
		p.state = P_Invalid 
	==>
		Send(GetSReq, HomeType, n, RequestChannel,UNDEFINED, UNDEFINED,UNDEFINED);
		p.state := P_IS_D;
	
	endrule;

	ruleset v:Value Do
		rule "Proc-Shared, store"
		(p.state = P_Shared)
		==>
			Send(GetMReq, HomeType, n, RequestChannel,UNDEFINED,UNDEFINED,UNDEFINED);
			p.state := P_SM_IaD;

		endrule;
	endruleset;



	rule "Proc-Shared, replacement"
		p.state = P_Shared
	==>
		Send(PutSReq, HomeType,n,RequestChannel,UNDEFINED,UNDEFINED,UNDEFINED);
		p.state := P_SI_Pa;

	endrule;

	ruleset  v: Value Do
		rule "Proc-Modified, replacement"
		(p.state = P_Modified)
	==>
		Send(PutMReq, HomeType,n,RequestChannel,v,UNDEFINED,UNDEFINED);
		p.state := P_MI_Pa;
		endrule;
		endruleset;
	ruleset v:Value Do
		rule "Proc-Exclusive, store"
		(p.state = P_Exclusive)
		==>
			--Send(GetMReq, HomeType, n, RequestChannel,UNDEFINED,UNDEFINED,UNDEFINED);
			p.state := P_Modified;

		endrule;
	endruleset;
	endalias;
endruleset;


-- Message delivery rules
ruleset n:Node do
	choose midx:Net[n] do
		alias chan:Net[n] do
		alias msg:chan[midx] do
		alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
		rule "receive-net"
			(isundefined(box[msg.vc].mtype))
		==>

			if IsMember(n, Home)
			then
				HomeReceive(msg);
			else
				ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
				box[msg.vc] := msg;
			endif;
		
			MultiSetRemove(midx, chan);
		
		endrule;
	
		endalias
		endalias;
		endalias;
	endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
		rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
		==>
			if IsMember(n, Home)
			then
				HomeReceive(InBox[n][vc]);
			else
				ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
				undefine InBox[n][vc];
			endif;
		
		endrule;
	endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
		-- home node initialization
		HomeNode.state := H_Invalid;
		undefine HomeNode.owner;
		HomeNode.val := v;
		undefine HomeNode.sharers;
	endfor;
	LastWrite := HomeNode.val;
	
	-- processor initialization
	for i:Proc do
		Procs[i].state := P_Invalid;
		undefine Procs[i].val;
		Procs[i].ackRecieved :=0;
		Procs[i].ackRequired :=0;
	endfor;

	-- network initialization
	undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
	HomeNode.state = H_Invalid
		->
			IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
		 HomeNode.state = H_Invalid 
		->
			HomeNode.val = LastWrite;

/*invariant "values in valid state match last write"
	Forall n : Proc Do	
		 Procs[n].state = P_Valid
		->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	*/
invariant "value is undefined while invalid"
	Forall n : Proc Do	
		 Procs[n].state = P_Invalid
		->
			IsUndefined(Procs[n].val)
	end;
		
-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
	HomeNode.state = H_Modified
		->
			MultiSetCount(i:HomeNode.sharers, true) = 0;



invariant "Invalid implies empty sharer list"
	HomeNode.state = H_Invalid
		->
			MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
	Forall n : Proc Do	
		 HomeNode.state = H_Shared | HomeNode.state = H_Invalid
		->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
	Forall n : Proc Do	
		 HomeNode.state = H_Shared & Procs[n].state = P_Shared
		->
			HomeNode.val = Procs[n].val
	end;

invariant "Exlusive implies empty sharers list"
	HomeNode.state = H_Exclusive
		->
			MultiSetCount(i:HomeNode.sharers, true) = 0;
invariant "Exlusive implies empty sharers list"
	HomeNode.state = H_Exclusive
		->
			!IsUndefined(HomeNode.owner);
invariant "Modified implies empty sharers list"
	HomeNode.state = H_Modified
		->
			!IsUndefined(HomeNode.owner);
