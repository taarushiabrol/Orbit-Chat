const API = "http://localhost:8080";
let currentUser = "";
let activeRecipient = "";
let friends = [];
let activeBlocked = false;
const $ = id => document.getElementById(id);
const messages = $("messages");
const toast = $("toast");

function initials(name){return name.split(/\s+/).map(x=>x[0]).join("").slice(0,2).toUpperCase();}
function notify(message){toast.textContent=message;toast.classList.add("show");clearTimeout(notify.timer);notify.timer=setTimeout(()=>toast.classList.remove("show"),2400);}
function addOutput(title, output, kind=""){
  const card=document.createElement("article");
  card.className="output-card "+kind;
  const head=document.createElement("div");head.className="output-head";
  const label=document.createElement("span");label.textContent=title.toUpperCase();
  head.append(label);
  const pre=document.createElement("pre");pre.textContent=output || "Done.";
  card.append(head,pre);messages.append(card);messages.scrollTop=messages.scrollHeight;
}
function renderBubble(text, mine, time=new Date().toLocaleTimeString([], {hour:"2-digit",minute:"2-digit"})){
  const bubble=document.createElement("div");bubble.className=`chat-bubble ${mine?"mine":"theirs"}`;
  const body=document.createElement("div");body.className="bubble-text";body.textContent=text;
  const meta=document.createElement("div");meta.className="bubble-meta";meta.textContent=time+(mine?"  ✓":"");
  bubble.append(body,meta);messages.append(bubble);messages.scrollTop=messages.scrollHeight;
}
function renderConversation(output){
  messages.innerHTML="";
  const lines=(output||"").split(/\r?\n/);
  let count=0;
  for(const line of lines){
    const match=line.match(/^\s*#\d+\s+t=\d+\s+(.+?)\s+->\s+(.+?)(?:\s+\[URGENT\])?:\s*(.*)$/);
    if(!match)continue;
    const sender=match[1], body=match[3];
    renderBubble(body,sender.toLowerCase()===currentUser.toLowerCase());count++;
  }
  if(!count){messages.innerHTML='<div class="conversation-empty"><div class="empty-symbol">✦</div><strong>Say hello</strong><span>Your messages with this person will appear here.</span></div>';
  }
}
async function apiCommand(command, title=command, kind="", silent=false){
  try{
    const response=await fetch(`${API}/api/command`,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({command})});
    const data=await response.json();
    if(!response.ok || !data.success){notify((data.output||"Something went wrong.").replace(/^Error:\s*/i,""));return null;}
    if(!silent)addOutput(title,data.output,kind);
    return data.output;
  }catch(error){
    notify("Could not connect. Please make sure the app is running and refresh.");
    return null;
  }
}
async function checkServer(){
  try{const r=await fetch(`${API}/api/health`);const d=await r.json();$("connectionText").textContent=d.status==="online"?"Connected":"Offline";$("connectionDot").classList.toggle("offline",d.status!=="online");return true;}
  catch{$("connectionText").textContent="Not connected";$("connectionDot").classList.add("offline");return false;}
}
function setLoggedIn(name){
  currentUser=name;$("currentUser").textContent=name;$("profileAvatar").textContent=initials(name);$("profileStatus").textContent="Available";
  $("logoutButton").hidden=false;
  $("authModal").classList.add("hidden");$("messageInput").disabled=false;$("sendButton").disabled=false;
  $("messageInput").placeholder="Write a message…";$("viewTitle").textContent="INBOX";
  messages.innerHTML="";
}
async function authRequest(action, username, password=""){
  try{
    const response=await fetch(`${API}/api/auth/${action}`,{
      method:"POST",
      headers:{"Content-Type":"application/json"},
      body:JSON.stringify({username,password})
    });
    const data=await response.json();
    return {ok:response.ok, data};
  }catch(error){
    notify("Could not connect. Please make sure Orbit is running.");
    return null;
  }
}
async function registerAndLogin(){
  const name=$("username").value.trim();
  const password=$("password").value;
  if(!/^[A-Za-z0-9_]{1,30}$/.test(name)){notify("Use 1–30 letters, numbers or underscores.");return;}
  if(password.length<6 || password.length>64){notify("Password must be 6–64 characters.");return;}
  $("registerButton").disabled=true;
  const result=await authRequest("register",name,password);
  $("registerButton").disabled=false;
  if(result?.ok && result.data.success){setLoggedIn(name);notify(`Welcome to Orbit, ${name}.`);}
  else $("authHint").textContent=result?.data?.message||"Could not create your account.";
}
async function login(){
  const name=$("username").value.trim();
  const password=$("password").value;
  if(!/^[A-Za-z0-9_]{1,30}$/.test(name) || !password){notify("Enter your username and password.");return;}
  const result=await authRequest("login",name,password);
  if(result?.ok && result.data.success){setLoggedIn(name);notify(`Welcome back, ${name}.`);}
  else $("authHint").textContent=result?.data?.message||"Incorrect username or password.";
}
function renderFriends(){
  const box=$("friendsList");box.innerHTML="";
  if(!friends.length){box.innerHTML='<p class="empty-side">Use + to add an existing user</p>';return;}
  friends.forEach(name=>{
    const row=document.createElement("div");row.className="friend";
    const av=document.createElement("div");av.className="avatar violet";av.textContent=initials(name);
    const label=document.createElement("span");label.textContent=name;
    row.append(av,label);row.addEventListener("click",()=>selectRecipient(name));box.append(row);
  });
}
async function selectRecipient(name){
  activeRecipient=name;
  activeBlocked=false;
  $("chatName").textContent=name;
  $("chatAvatar").textContent=initials(name);
  $("chatSubtitle").textContent=`Direct conversation · logged in as ${currentUser}`;
  $("messageInput").placeholder=`Message ${name}…`;
  $("blockButton").hidden=false;
  $("blockButton").disabled=true;
  $("blockButton").textContent="Checking…";
  const status=await blockStatus(name);
  activeBlocked=!!status?.blocked;
  updateBlockUI();
  if(!activeBlocked){const history=await apiCommand(`open ${name}`,"", "", true);if(history!==null)renderConversation(history);}
  else messages.innerHTML=`<div class="conversation-empty"><strong>Conversation blocked</strong><span>Unblock ${name} to send messages.</span></div>`;
  notify(`Conversation with ${name} opened.`);
}
async function blockStatus(target){
  try{
    const r=await fetch(`${API}/api/block/status`,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({target})});
    return await r.json();
  }catch{return null;}
}
function updateBlockUI(){
  const button=$("blockButton");
  if(!activeRecipient || !currentUser){button.hidden=true;return;}
  button.hidden=false;
  button.disabled=false;
  button.textContent=activeBlocked?"Unblock":"Block";
  button.classList.toggle("is-blocked",activeBlocked);
  $("messageInput").disabled=activeBlocked;
  $("sendButton").disabled=activeBlocked;
  $("messageInput").placeholder=activeBlocked?`You blocked ${activeRecipient}`:`Message ${activeRecipient}…`;
  $("chatSubtitle").textContent=activeBlocked?`Blocked · ${currentUser}`:`Direct conversation · logged in as ${currentUser}`;
}
async function toggleBlock(){
  if(!currentUser||!activeRecipient)return;
  const nextAction=activeBlocked?"unblock":"block";
  const confirmed=confirm(activeBlocked?`Unblock ${activeRecipient}?`:`Block ${activeRecipient}? They won't be able to message you, and messages between you will be rejected.`);
  if(!confirmed)return;
  const button=$("blockButton");button.disabled=true;button.textContent="Please wait…";
  try{
    const r=await fetch(`${API}/api/${nextAction}`,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({target:activeRecipient})});
    const d=await r.json();
    if(r.ok&&d.success){
      activeBlocked=!!d.blocked;updateBlockUI();
      notify(activeBlocked?`${activeRecipient} blocked.`:`${activeRecipient} unblocked.`);
      if(activeBlocked)messages.innerHTML=`<div class="system-note">You blocked ${activeRecipient}. Messages in this conversation are disabled.</div>`;
      else messages.innerHTML=`<div class="system-note">You unblocked ${activeRecipient}. You can message again.</div>`;
    }else{button.disabled=false;updateBlockUI();notify(d.message||"Could not update block status.");}
  }catch{button.disabled=false;updateBlockUI();notify("Could not connect to Orbit.");}
}
async function loadAction(action){
  if(!currentUser){notify("Log in first.");return;}
  const labels={inbox:"Inbox",history:"Message history",recent:"Recent chats",suggest:"Friend suggestions",communities:"Communities",rooms:"Chat rooms"};
  $("viewTitle").textContent=(labels[action]||action).toUpperCase();messages.innerHTML="";
  if(action==="inbox")await apiCommand("inbox","Your inbox");
  else if(action==="history")await apiCommand("history","Message history");
  else if(action==="recent")await apiCommand("recent","Recent conversations");
  else if(action==="suggest")await apiCommand("suggest","People you may know");
  else if(action==="communities")await apiCommand("communities","Your communities");
  else if(action==="rooms")await apiCommand("rooms","Group chats");
}
$("authForm").addEventListener("submit",e=>{e.preventDefault();login();});
$("registerButton").addEventListener("click",registerAndLogin);
$("switchUser").addEventListener("click",()=>{$("authModal").classList.remove("hidden");$("authHint").textContent="Switch to another account.";});

$("blockButton").addEventListener("click",toggleBlock);

$("logoutButton").addEventListener("click",async()=>{
  await authRequest("logout", currentUser);
  currentUser="";
  activeRecipient="";
  activeBlocked=false;
  $("blockButton").hidden=true;
  friends=[];
  $("currentUser").textContent="Not logged in";
  $("profileAvatar").textContent="?";
  $("profileStatus").textContent="Your account";
  $("logoutButton").hidden=true;
  $("chatName").textContent="Your messages";
  $("chatAvatar").textContent="◈";
  $("chatSubtitle").textContent="Choose a conversation to get started";
  $("messageInput").value="";
  $("messageInput").disabled=true;
  $("sendButton").disabled=true;
  $("messageInput").placeholder="Choose a conversation first…";
  $("viewTitle").textContent="ALL MESSAGES";
  messages.innerHTML='<div class="welcome-card"><div class="welcome-icon">✦</div><h2>You are signed out.</h2><p>Log in again whenever you are ready to continue chatting.</p></div>';
  renderFriends();
  $("username").value="";
  $("password").value="";
  $("authHint").textContent="You have been logged out safely on this device.";
  $("authModal").classList.remove("hidden");
  notify("You have been logged out.");
});

$("addFriend").addEventListener("click",async()=>{
  if(!currentUser){notify("Log in first.");return;}
  const name=prompt("Enter the exact username of an existing account:");
  if(!name||!name.trim())return;
  const clean=name.trim();
  const result=await apiCommand(`friend ${clean}`,"Contact added");
  if(result!==null && !/login first|usage:|unknown user/i.test(result)){if(!friends.includes(clean))friends.push(clean);renderFriends();selectRecipient(clean);}
});
$("recipientButton").addEventListener("click",()=>{
  const name=prompt("Enter an existing username to message:");
  if(name&&name.trim())selectRecipient(name.trim());
});
$("messageForm").addEventListener("submit",async e=>{
  e.preventDefault();const input=$("messageInput");const value=input.value.trim();
  if(!currentUser){notify("Log in first.");return;}
  if(!activeRecipient){notify("Choose someone to chat with first.");return;}
  if(activeBlocked){notify("Unblock this person before sending messages.");return;}
  if(!value)return;
  const command=`send ${activeRecipient} ${value}`;
  const result=await apiCommand(command,"", "", true);
  if(result!==null && /queued/i.test(result)){renderBubble(value,true);input.value="";await apiCommand("process","", "", true);}
});
document.querySelectorAll(".nav-item").forEach(button=>button.addEventListener("click",()=>{
  document.querySelectorAll(".nav-item").forEach(x=>x.classList.remove("active"));button.classList.add("active");loadAction(button.dataset.action);
}));
(async()=>{const online=await checkServer();if(!online){$("authHint").textContent="Please start the app and refresh this page.";notify("Could not connect to Orbit.");}})();
