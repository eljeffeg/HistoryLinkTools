#!/usr/bin/env python
#
# Copyright 2012-2019 Jeff Gentes
#

#Python client library for the Geni Platform.

import re
import traceback
import cookielib
import base64
import functools
import json
import hashlib
import hmac
import time
import logging
import os
import httplib #for custom error handler
import threading
import torndb
import tornado.escape
import tornado.httpclient
import tornado.ioloop
import tornado.web
import tornado.wsgi
import urllib
import urllib2
import urlparse
import random
from operator import itemgetter
from collections import Iterable
from tornado.options import define, options
from tornado import gen
from tornado.web import asynchronous
from datetime import datetime, timedelta
from node import Node
from tree import Tree
import time

import geni

# Find a JSON parser
try:
    import simplejson as json
except ImportError:
    try:
        from django.utils import simplejson as json
    except ImportError:
        import json
_parse_json = json.loads

define("compiled_css_url")
define("compiled_jquery_url")
define("config")
define("cookie_secret")
define("debug", type=bool, default=True)
define("mysql_host")
define("mysql_database")
define("mysql_user")
define("mysql_password")
define("historylink_id")
define("historylink_secret")
define("historylink_canvas_id")
define("service_token")
define("listenport", type=int)
define("silent", type=bool)
define("historyprofiles", type=set)
define("historycache", type=dict)
define("countrycodes", type=dict)
define("statecodes", type=dict)

#class GeniApplication(tornado.wsgi.WSGIApplication):
class GeniApplication(tornado.web.Application):
    def __init__(self):
        self.linkHolder = LinkHolder()
        base_dir = os.path.dirname(__file__)
        canvas_id = options.historylink_canvas_id
        app_id = options.historylink_id
        geni_secret = options.historylink_secret
        settings = {
            "cookie_secret": options.cookie_secret,
            "static_path": os.path.join(base_dir, "static"),
            "template_path": os.path.join(base_dir, "templates"),
            "debug": options.debug,
            "geni_canvas_id": canvas_id,
            "geni_app_id": app_id,
            "geni_secret": geni_secret,
            "ui_modules": {
                "TimeConvert": TimeConvert,
                "SHAHash": SHAHash,
            },
        }

        #tornado.wsgi.WSGIApplication.__init__(self, [
        tornado.web.Application.__init__(self, [
            tornado.web.url(r"/", HomeHandler, name="home"),
            tornado.web.url(r"/projects", ProjectHandler, name="project"),
            tornado.web.url(r"/history", HistoryHandler, name="history"),
            tornado.web.url(r"/graph", GraphHandler, name="graph"),
            tornado.web.url(r"/privacy", PrivacyHandler, name="privacy"),
             tornado.web.url(r"/bio", BioHandler, name="bio"),
            tornado.web.url(r"/graphprocess", GraphProcess),
            tornado.web.url(r"/graphcount", GraphCount),
            tornado.web.url(r"/graphlist", GraphList),
            tornado.web.url(r"/graphrender", GraphRender, name="graphrender"),
            tornado.web.url(r"/graphjs.svg", GraphJS),
            tornado.web.url(r"/historylist", HistoryList),
            tornado.web.url(r"/historycount", HistoryCount),
            tornado.web.url(r"/historyprocess", HistoryProcess),
            tornado.web.url(r"/projectupdate", ProjectUpdate),
            tornado.web.url(r"/projectsubmit", ProjectSubmit),
            tornado.web.url(r"/projectlist", ProjectList),
            tornado.web.url(r"/treecomplete", TreeComplete),
            tornado.web.url(r"/leaderboard", LeaderBoard),
            tornado.web.url(r"/leaderupdate", LeaderUpdate),
            tornado.web.url(r"/leaderadd", LeaderAdd),
            tornado.web.url(r"/account", AccountRequest),
            tornado.web.url(r"/login", LoginHandler, name="login"),
            tornado.web.url(r"/logout", LogoutHandler, name="logout"),
            tornado.web.url(r"/geni", GeniCanvasHandler),
        ], **settings)


class ErrorHandler(tornado.web.RequestHandler):
    """Generates an error response with status_code for all requests."""

    def __init__(self, application, request, status_code):
        tornado.web.RequestHandler.__init__(self, application, request)
        self.set_status(status_code)

    def get_error_html(self, status_code, **kwargs):
        self.require_setting("static_path")
        if status_code in [404, 500, 503, 403]:
            filename = os.path.join(self.settings['static_path'], '%d.html' % status_code)
            if os.path.exists(filename):
                f = open(filename, 'r')
                data = f.read()
                f.close()
                return data
        return "<html><title>%(code)d: %(message)s</title>" \
               "<body class='bodyErrorPage'>%(code)d: %(message)s</body></html>" % {
                   "code": status_code,
                   "message": httplib.responses[status_code],
               }

    def prepare(self):
        raise tornado.web.HTTPError(self._status_code)

## override the tornado.web.ErrorHandler with our default ErrorHandler
tornado.web.ErrorHandler = ErrorHandler


class LinkHolder(object):
    cookie = {}

    def set(self, id, key, value):
        if not id in self.cookie:
            self.cookie[id] = {}
        self.cookie[id][key] = value

    def clear_matches(self, id):
        if not id in self.cookie:
            self.cookie[id] = {}
        self.cookie[id]["matches"] = []
        self.cookie[id]["parentmatches"] = {}
        self.cookie[id]["gencount"] = {}
        self.cookie[id]["history"] = set([])
        self.cookie[id]["familyroot"] = []

    def add_matches(self, id, profile):
        if not id in self.cookie:
            self.cookie[id] = {}
        if not "matches" in self.cookie[id]:
            self.cookie[id]["matches"] = []
        exists = None
        if "hits" in self.cookie[id]:
            self.cookie[id]["hits"] += 1
        else:
            self.cookie[id]["hits"] = 1
        message = None
        for items in self.cookie[id]["matches"]:
            if items["id"] == profile["id"]:
                #Give more weight to parents over aunts/uncles
                exists = True
                if "aunt" in profile["relation"]:
                    pass
                elif "uncle" in profile["relation"]:
                    pass
                elif "mother" in items["relation"]:
                    pass
                elif "father" in items["relation"]:
                    pass
                else:
                    items["relation"] = profile["relation"]

                if profile["message"] == "Master Profile" and items["message"] == "Master Profile":
                    message = True
                    break
                elif profile["message"] == "Non-Master Public" and items["message"] == "Non-Master Public":
                    message = True
                    break
                elif profile["message"] == "Parent Conflict" and items["message"] == "Parent Conflict":
                    message = True
                    break
                elif profile["message"] == "Merge Pending" and items["message"] == "Merge Pending":
                    message = True
                    break

        if not exists:
            self.cookie[id]["matches"].append(profile)
        elif profile["message"] and not message:
            self.cookie[id]["matches"].append(profile)
            exists = False

        return exists

    def add_parentmatch(self, id, gen, profile):
        if not id in self.cookie:
            self.cookie[id] = {}
        if not "parentmatches" in self.cookie[id]:
            self.cookie[id]["parentmatches"] = {}
        if not gen in self.cookie[id]["parentmatches"]:
            self.cookie[id]["parentmatches"][gen] = {}
        if not profile in self.cookie[id]["parentmatches"][gen]:
            self.cookie[id]["parentmatches"][gen][profile] = 1
        else:
            self.cookie[id]["parentmatches"][gen][profile] += 1

    def get_parentmatch(self, id, gen, profile):
        if not id in self.cookie:
            return 0
        if not "parentmatches" in self.cookie[id]:
            return 0
        if not gen in self.cookie[id]["parentmatches"]:
            return 0
        if not profile in self.cookie[id]["parentmatches"][gen]:
            return 0
        return self.cookie[id]["parentmatches"][gen][profile]

    def remove_parentmatch(self, id, gen):
        if not id in self.cookie:
            return
        if not "parentmatches" in self.cookie[id]:
            return
        if not gen in self.cookie[id]["parentmatches"]:
            return
        else:
            self.cookie[id]["parentmatches"][gen] = {}
        return

    def get_matches(self, id):
        if not id in self.cookie:
            return []
        if not "matches" in self.cookie[id]:
            return []
        return self.cookie[id]["matches"]

    def get_matchcount(self, id):
        if not id in self.cookie:
            return 0
        if not "matches" in self.cookie[id]:
            return 0
        return len(self.cookie[id]["matches"])

    def addParentCount(self, id, gen, parentcount, mastercount):
        if not id in self.cookie:
            self.cookie[id] = {}
        if not "gencount" in self.cookie[id]:
            self.cookie[id]["gencount"] = {}
        if not str(gen) in self.cookie[id]["gencount"]:
            self.cookie[id]["gencount"][str(gen)] = {}
            self.cookie[id]["gencount"][str(gen)]["count"] = parentcount
            self.cookie[id]["gencount"][str(gen)]["mpcount"] = mastercount
            self.cookie[id]["gencount"][str(gen)]["label"] = str(self.getGeneration(gen)) + "s"
        else:
            self.cookie[id]["gencount"][str(gen)]["count"] += parentcount
            self.cookie[id]["gencount"][str(gen)]["mpcount"] += mastercount

    def getParentCount(self, id):
        if not id in self.cookie:
            return None
        if not "gencount" in self.cookie[id]:
            return None
        return self.cookie[id]["gencount"]

    def set_familyroot(self, id, root):
        if not id in self.cookie:
            self.cookie[id] = {}
        self.cookie[id]["familyroot"] = root

    def append_familyroot(self, id, profile):
        if not id in self.cookie:
            self.cookie[id] = {}
        if not "familyroot" in self.cookie[id]:
            self.cookie[id]["familyroot"] = []
        if not profile in self.cookie[id]["familyroot"]:
            self.cookie[id]["familyroot"].append(profile)

    def get_familyroot(self, id):
        if not id in self.cookie:
            return []
        if not "familyroot" in self.cookie[id]:
            return []
        return self.cookie[id]["familyroot"]

    def add_history(self, id, history):
        if not id in self.cookie:
            self.cookie[id] = {}
        if not "history" in self.cookie[id]:
            self.cookie[id]["history"] = set(history)
        else:
            self.cookie[id]["history"].update(history)

    def get_history(self, id):
        if not id in self.cookie:
            return set([])
        if not "history" in self.cookie[id]:
            return set([])
        return self.cookie[id]["history"]

    def reset_matchhit(self, id):
        if not id in self.cookie:
            return
            #if "matches" in self.cookie[id]:
            #self.cookie[id]["matches"] = []
        if "hits" in self.cookie[id]:
            self.cookie[id]["hits"] = 0
        return

    def reset(self, id):
        if not id in self.cookie:
            self.cookie[id] = {}
        self.cookie[id]["hits"] = 0
        self.cookie[id]["count"] = 0
        self.cookie[id]["mpcount"] = 0
        self.cookie[id]["pending"] = 0
        self.cookie[id]["pconflict"] = 0
        self.cookie[id]["stage"] = "parent's family"
        self.clear_matches(id)

    def get(self, id, key):
        if id in self.cookie:
            if key in self.cookie[id]:
                return self.cookie[id][key]
        if key == "count":
            return 0
        elif key == "mpcount":
            return 0
        elif key == "pending":
            return 0
        elif key == "problems":
            return 0
        elif key == "pconflict":
            return 0
        elif key == "stage":
            return "parent's family"
        elif key == "running":
            return 0
        elif key == "graphrunning":
            return 0
        elif key == "hits":
            return 0
        else:
            return None

    def getGeneration(self, gen):
        stage = "parent"
        if gen < 0:
            stage = "profile"
        elif gen == 1:
            stage = "grand parent"
        elif gen == 2:
            stage = "great grandparent"
        elif gen > 2:
            stage = self.genPrefix(gen) + " great grandparent"
        return stage

    def genPrefix(self, gen):
        gen -= 1
        value = ""
        if gen == 2:
            value = str(gen) + "nd"
        elif gen == 3:
            value = str(gen) + "rd"
        elif gen > 3:
            if gen < 21:
                value = str(gen) + "th"
            elif gen % 10 == 1:
                value = str(gen) + "st"
            elif gen % 10 == 2:
                value = str(gen) + "nd"
            elif gen % 10 == 3:
                value = str(gen) + "rd"
            else:
                value = str(gen) + "th"
        return value

    def stop(self, id):
        if id and id in self.cookie:
            if "running" in self.cookie[id]:
                self.cookie[id]["running"] = 0
            self.reset(id)


class BaseHandler(tornado.web.RequestHandler):
    @property
    def backend(self):
        return Backend.instance()

    def prepare(self):
        self.set_header('P3P', 'CP="HONK"')
        if self.request.protocol == "http":
            self.redirect("https://%s" % self.request.full_url()[len("http://"):], permanent=True)

    def write_error(self, status_code, **kwargs):
        import traceback

        if self.settings.get("debug") and "exc_info" in kwargs:
            exc_info = kwargs["exc_info"]
            trace_info = ''.join(["%s<br/>" % line for line in traceback.format_exception(*exc_info)])
            request_info = ''.join(
                ["<strong>%s</strong>: %s<br/>" % (k, self.request.__dict__[k] ) for k in self.request.__dict__.keys()])
            error = exc_info[1]
            self.set_header('Content-Type', 'text/html')
            try:
                self.finish("""<html>
                                 <title>%s</title>
                                 <body>
                                    <h2>Error</h2>
                                    <p>%s</p>
                                    <h2>Traceback</h2>
                                    <p>%s</p>
                                    <h2>Request Info</h2>
                                    <p>%s</p>
                                 </body>
                               </html>""" % (error, error,
                                             trace_info, request_info))
            except:
                self.finish()

    def get_current_user(self):
        if not self.get_secure_cookie("uid"):
            return None
        if self.get_secure_cookie("uid") == "":
            return None
        user = {'id': self.get_secure_cookie("uid"), 'access_token': self.get_secure_cookie("access_token"),
                'refresh_token': self.get_secure_cookie("refresh_token"),
                'name': self.get_secure_cookie("name"), 'account_type': self.get_secure_cookie("account_type"),
                'curator': self.get_secure_cookie("curator"), 'big_tree': self.get_secure_cookie("big_tree")}
        return user


    def login(self, next):
        if not self.current_user:
            logging.info("Need user grant permission, redirect to oauth dialog.")
            oauth_url = self.get_login_url(next)
            logging.info(oauth_url)
            self.render("oauth.html", oauth_url=oauth_url)
        else:
            return

    def get_refresh_token(self, next=None):
        if not next:
            next = self.request.full_url()
        if not next.startswith("http://") and not next.startswith("https://") and \
                not next.startswith("http%3A%2F%2F") and not next.startswith("https%3A%2F%2F"):
            next = urlparse.urljoin(self.request.full_url(), next)
        next = next.replace("http:", self.request.protocol + ":")
        user = self.current_user
        if user and "refresh_token" in user:
            redirect_uri = self.request.protocol + "://" + self.request.host + self.request.uri
            refresh = "https://www.geni.com/platform/oauth/request_token?" + urllib.urlencode({
                "refresh_token": user["refresh_token"],
                "grant_type": "refresh_token",
                "redirect_uri": redirect_uri,
                "client_id": self.settings.get("geni_app_id"),
                "client_secret": self.settings.get("geni_secret"),
                })
            response = urllib.urlopen(refresh)
            redata = response.read()
            if "error" in redata:
                return self.get_login_url(next)
            else:
                mytoken = json.loads(redata)
                self.set_secure_cookie("access_token", mytoken["access_token"])
                self.set_secure_cookie("refresh_token", mytoken["refresh_token"])
            return next
        else:
            return self.get_login_url(next)

    def get_login_url(self, next=None):
        if not next:
            next = self.request.full_url()
        if not next.startswith("http://") and not next.startswith("https://") and \
                not next.startswith("http%3A%2F%2F") and not next.startswith("https%3A%2F%2F"):
            next = urlparse.urljoin(self.request.full_url(), next)
        code = self.get_argument("code", None)
        next = next.replace("http:", self.request.protocol + ":")
        if code:
            return self.request.protocol + "://" + self.request.host + \
                   self.reverse_url("login") + "?" + urllib.urlencode({
                "next": next,
                "code": code,
                })
        redirect_uri = self.request.protocol + "://" + self.request.host + \
                       self.reverse_url("login") + "?" + urllib.urlencode({"next": next})
        loginurl = "https://www.geni.com/platform/oauth/authorize?" + urllib.urlencode({
            "client_id": self.settings.get("geni_app_id"),
            "redirect_uri": redirect_uri,
            })
        #if next.endswith("smartlogin"):
        #loginurl = loginurl + "&" + urllib.urlencode({"display": "popup"})
        return loginurl

    def write_json(self, obj):
        self.set_header("Content-Type", "application/json; charset=UTF-8")
        self.finish(json.dumps(obj))

    def render(self, template, **kwargs):
        kwargs["error_message"] = self.get_secure_cookie("message")
        if kwargs["error_message"]:
            kwargs["error_message"] = base64.b64decode(kwargs["error_message"])
            self.clear_cookie("message")
        tornado.web.RequestHandler.render(self, template, **kwargs)

    def set_error_message(self, message):
        self.set_secure_cookie("message", base64.b64encode(message))

    def isCurator(self, usecookie=None, user=None):
        if not user:
            user = self.current_user
        if user:
            if usecookie and "curator" in user:
                if user["curator"]:
                    return user["curator"]
            if "id" in user:
                curator = self.backend.get_curators(user["id"])
                if len(curator) > 0:
                    return True
        return False

    def isAuthorized(self, user=None):
        details = True
        if not user:
            details = False
            user = self.current_user
        if user and "id" in user:
            access = self.backend.get_smartaccess(user["id"], details)
            if len(access) > 0:
                if details:
                    return json.dumps(access[0])
                else:
                    return "true"
        return "false"

    def isPro(self, user=None):
        selfcheck = False
        if not user:
            selfcheck = True
            user = self.current_user
        if user and "account_type" in user and user["account_type"] == "pro":
            return True
        if selfcheck and user and "id" in user:
            profileinfo = self.backend.get_profile(user["id"], user)
            if profileinfo and "account_type" in profileinfo and profileinfo["account_type"] == "pro":
                user["account_type"] = "pro"
                return True
        return False

    def isClaimed(self, user=None):
        if not user:
            user = self.current_user
        if user and "claimed" in user:
            return user["claimed"]
        return False

    def inBigTree(self, user=None):
        if not user:
            user = self.current_user
        if user and "big_tree" in user:
            return user["big_tree"]
        return False


class AccountRequest(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        profile = self.get_argument("profile", None)
        action = self.get_argument("action", None)
        if action and profile:
            curator = self.isCurator()
            if curator:
                user = self.current_user
                profileinfo = self.backend.get_profile(profile, user)
                if "id" in profileinfo and "id" in user:
                    if action == "add_user":
                        self.backend.add_smartaccess(profileinfo["id"], user["id"])
                    elif action == "revoke_user":
                        self.backend.remove_smartaccess(profileinfo["id"], user["id"])
        else:
            if profile:
                user = self.current_user
                profileinfo = self.backend.get_profile(profile, user)
                bigtree = self.inBigTree(profileinfo)
                authorized = self.isAuthorized(profileinfo)
                pro = self.isPro(profileinfo)
                claimed = self.isClaimed(profileinfo)
                curator = self.isCurator(False, profileinfo)
            else:
                claimed = True
                curator = self.isCurator(True)
                if curator:
                    #skip unnecessary request if curator
                    self.set_secure_cookie("curator", "True")
                    pro = True
                    authorized = "true"
                    bigtree = True
                else:
                    pro = self.isPro()
                    authorized = self.isAuthorized()
                    bigtree = self.inBigTree()
            self.write('{"curator": ' + str(curator).lower() + ', "pro": ' + str(pro).lower() + ', "big_tree": ' + str(bigtree).lower() + ', "user": ' + authorized + ', "claimed": ' + str(claimed).lower() + '}')
        self.finish()


class HomeHandler(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        self.render("home.html")


class LeaderBoard(BaseHandler):
    @tornado.web.asynchronous
    @tornado.web.authenticated
    def get(self):
        user = self.current_user
        try:
            logging.info("*** " + str(user["name"]) + " checked leaderboard")
        except:
            logging.info("*** " + str(user["id"]) + " checked leaderboard")

        totals = self.get_argument("totals", None)
        timeframe = self.get_argument("timeframe", None)

        try:
            page = int(self.get_argument("page", 1))
        except:
            page = 1
        d = datetime.now()
        d.replace(day=15)
        nowframe = str(d.year) + "-" + str('%02d' % d.month)
        if timeframe:
            d = datetime.strptime(timeframe + "-15", "%Y-%m-%d")
            if d.year > 2012 or (d.year == 2012 and d.month > 2):
                pass
            else:
                d = datetime.now()
                d.replace(day=15)
        currentframe = str(d.year) + "-" + str('%02d' % d.month)
        backframe = None
        nextframe = None
        bd = d - timedelta(days=30)

        if bd.year > 2012 or (bd.year == 2012 and bd.month > 2):
            backframe = str(bd.year) + "-" + str('%02d' % bd.month)
        if nowframe != currentframe:
            fd = d + timedelta(days=30)
            nextframe = str(fd.year) + "-" + str('%02d' % fd.month)

        #profile = self.backend.get_profile(user["id"], user)
        curator = self.isCurator()

        if curator:
            if not totals:
                mergeleaders = self.backend.get_merge_leaders(currentframe)
                updateleaders = self.backend.get_update_leaders(currentframe)
                additionleaders = self.backend.get_add_leaders(currentframe)
                documentleaders = self.backend.get_doc_leaders(currentframe)
                projectleaders = self.backend.get_project_leaders(currentframe)
                curatorcounts = self.backend.get_curator_counts(currentframe)
            else:
                mergeleaders = self.backend.get_merge_total()
                updateleaders = self.backend.get_update_total()
                additionleaders = self.backend.get_add_total()
                documentleaders = self.backend.get_doc_total()
                projectleaders = self.backend.get_project_total()
                curatorcounts = self.backend.get_curator_total()
            updatetime = self.backend.get_leaderupdate()
            if curatorcounts[0]["merges"]:
                mergecount = "{:,}".format(curatorcounts[0]["merges"])
            else:
                mergecount = 0
            if curatorcounts[0]["updates"]:
                updatecount = "{:,}".format(curatorcounts[0]["updates"])
            else:
                updatecount = 0
            if curatorcounts[0]["additions"]:
                addcount = "{:,}".format(curatorcounts[0]["additions"])
            else:
                addcount = 0
            if curatorcounts[0]["documentation"]:
                doccount = "{:,}".format(curatorcounts[0]["documentation"])
            else:
                doccount = 0
            if curatorcounts[0]["projects"]:
                projectcount = "{:,}".format(curatorcounts[0]["projects"])
            else:
                projectcount = 0

            totalleaders = {}
            for idx, usr in enumerate(mergeleaders):
                if usr["id"] in totalleaders:
                    value = (100 - idx) + totalleaders[usr["id"]]
                else:
                    value = 100 - idx
                totalleaders[usr["id"]] = {"total": value, "mug": usr["mug"], "name": usr["name"], "id": usr["id"]}
            for idx, usr in enumerate(updateleaders):
                if usr["id"] in totalleaders:
                    value = (100 - idx) + totalleaders[usr["id"]].get("total")
                else:
                    value = 100 - idx
                totalleaders[usr["id"]] = {"total": value, "mug": usr["mug"], "name": usr["name"], "id": usr["id"]}
            for idx, usr in enumerate(additionleaders):
                if usr["id"] in totalleaders:
                    value = (100 - idx) + totalleaders[usr["id"]].get("total")
                else:
                    value = 100 - idx
                totalleaders[usr["id"]] = {"total": value, "mug": usr["mug"], "name": usr["name"], "id": usr["id"]}
            for idx, usr in enumerate(documentleaders):
                if usr["id"] in totalleaders:
                    value = (100 - idx) + totalleaders[usr["id"]].get("total")
                else:
                    value = 100 - idx
                totalleaders[usr["id"]] = {"total": value, "mug": usr["mug"], "name": usr["name"], "id": usr["id"]}
            for idx, usr in enumerate(projectleaders):
                if usr["id"] in totalleaders:
                    value = (100 - idx) + totalleaders[usr["id"]].get("total")
                else:
                    value = 100 - idx
                totalleaders[usr["id"]] = {"total": value, "mug": usr["mug"], "name": usr["name"], "id": usr["id"]}
            newleaders = []
            for item in totalleaders:
                newleaders.append(totalleaders[item])
            totalleaders = []
            sortedleaders = sorted(newleaders, key=itemgetter("total"), reverse=True)
            newleaders = None
            for idx, item in enumerate(sortedleaders):
                if idx < 100:
                    totalleaders.append(item)
            sortedleaders = None
            rawstats = self.backend.get_curator_stats()
            curatorstats = "['Month','Merges','Updates','Tree Building','Documents','Projects'],"
            for stat in rawstats:
                curatorstats = curatorstats + "['" + str(stat["timeframe"]) + "'," + str(stat["merges"]) + "," + str(
                    stat["updates"]) + "," + str(stat["additions"]) + "," + str(stat["documentation"]) + "," + str(
                    stat["projects"]) + "],"
            curatorstats = curatorstats.rstrip(',')
            self.render("leaderboard.html", mergeleaders=mergeleaders, updateleaders=updateleaders,
                        mergecount=mergecount, updatecount=updatecount, updatetime=updatetime, timeframe=currentframe,
                        backframe=backframe, nextframe=nextframe, curatorstats=curatorstats, totals=totals,
                        additionleaders=additionleaders, documentleaders=documentleaders, projectleaders=projectleaders,
                        totalleaders=totalleaders, addcount=addcount, doccount=doccount, projectcount=projectcount,
                        page=page)
        else:
            self.write(
                "This page is only available for Curators and Geni Staff.  If you're one of these and want access, <a href='https://www.geni.com/profile-16675621'>send me a message</a>.")
            self.finish()


class LeaderAdd(BaseHandler):
    @tornado.web.asynchronous
    @tornado.web.authenticated
    def get(self):
        user = self.current_user
        f = open('curators.html', 'r')
        filestring = f.read()
        f.close()
        r = re.findall('/people/(.*?)&amp;', filestring, re.DOTALL)
        profiles = []
        for item in r:
            part = item.split("/")
            guid = "g" + str(part[1])
            profile = self.backend.get_profile(guid, user)
            mug = profile["mugshot_urls"]["thumb2"]
            if "display_name" in profile:
                name = profile["display_name"]
            else:
                name = profile["name"]
            id = profile["id"]
            self.backend.update_leaderboard(id, name, mug)

        self.write("update initiated")
        self.finish()


class LeaderUpdate(BaseHandler):
    @tornado.web.asynchronous
    @tornado.web.authenticated
    def get(self):
        user = self.current_user
        try:
            validate = "https://www.geni.com/platform/oauth/validate_token?" + urllib.urlencode({
                "access_token": user["access_token"],
            })
            response = urllib.urlopen(validate)
            redata = response.read()
            if "error" in redata:
                self.redirect(self.get_refresh_token(self.request.uri))
                return
        except:
            self.redirect(self.get_login_url(self.request.uri))
            return
        self.render("leaderupdate.html")
        profiles = self.backend.get_curators()
        mergelist = ["profile.merge"]
        updatelist = ["profile.update", "union.update", "union.set-birth-orders",
                      "profile.set-marriage-orders", "surname.update", "profile.update-meta", "profile.remove-manager",
                      "profile.update-family-settings", "profile.lock-fields"]
        documentlist = ["photo.add-tag", "photo.delete-tag", "photo.update-tag", "document.add-tag",
                        "document.delete-tag", "video.add-tag", "video.remove-tag", "marriage.remove-attendee",
                        "marriage.add-attendee", "death.add-attendee", "death.remove-attendee",
                        "divorce.remove-attendee", "divorce.add-attendee"]
        addlist = ["profile.add", "union.add-partner", "union.add-child", "union.add-parent", "union.add-sibling",
                   "profile.add-parent", "profile.add-partner", "profile.add-sibling", "profile.add-child",
                   "profile.delete",
                   "profile.undelete", "profile.delete-edge", "profile.set-parents"]
        projectlist = ["project.update", "project.add", "project.remove-user", "project.remove-profile",
                       "project.remove-label",
                       "project.add-label", "project.add-profile", "project.add-user", "project.delete"]


        insertstatement = ""
        updatecount = 0
        cookiepath = os.path.join(os.path.dirname(os.path.realpath(__file__)), "cookies.txt")
        cj = cookielib.MozillaCookieJar(cookiepath)
        cj.load()
        opener = urllib2.build_opener(urllib2.HTTPCookieProcessor(cj))
        for person in profiles:
            if person["userid"]:
                try:
                    logging.info(str(person["name"]))
                except:
                    logging.info(str(person["userid"]))
                userid = person["userid"]
                id = person["id"]

                dataurl = "https://www.geni.com/revisions/user_histogram_data?" + urllib.urlencode({
                    "user_id": userid,
                    "access_token": user["access_token"]
                })
                r = []
                try:
                    #print(opener.open(dataurl).read())
                    histogramdata = opener.open(dataurl).read()
                    try:
                        r = json.loads(histogramdata)
                    except:
                        logging.info("   * Problem reading JSON *")
                        logging.info(histogramdata)
                        continue
                    mergeidx = []
                    updateidx = []
                    addidx = []
                    projectidx = []
                    documentidx = []

                    for idx, item in enumerate(r[0]):
                        if item in mergelist:
                            mergeidx.append(idx)
                        if item in updatelist:
                            updateidx.append(idx)
                        if item in addlist:
                            addidx.append(idx)
                        if item in projectlist:
                            projectidx.append(idx)
                        if item in documentlist:
                            documentidx.append(idx)

                    for idx, x in enumerate(r):
                        if idx > len(r) - 3:
                            try:

                                merges = 0
                                updates = 0
                                additions = 0
                                projects = 0
                                documents = 0

                                timeframe = x[0]
                                if timeframe == "Month":
                                    continue
                                #run = None
                                #if timeframe.startswith("2013"):
                                #run = True
                                #elif timeframe.startswith("2012") and not (timeframe.endswith("01") or timeframe.endswith("02")):
                                #run = True
                                if 1 == 1:
                                    for subidx in mergeidx:
                                        merges = merges + x[subidx]
                                    for subidx in updateidx:
                                        updates = updates + x[subidx]
                                    for subidx in addidx:
                                        additions = additions + x[subidx]
                                    for subidx in projectidx:
                                        projects = projects + x[subidx]
                                    for subidx in documentidx:
                                        documents = documents + x[subidx]
                                    insertstatement += 'INSERT INTO leaderstats (id, timeframe, merges, updates, additions, document, projects) VALUES ("%s","%s",%s,%s,%s,%s,%s) ON DUPLICATE KEY UPDATE merges=%s,updates=%s,additions=%s,document=%s,projects=%s;\n' % (
                                        id, timeframe, merges, updates, additions, documents, projects, merges, updates,
                                        additions, documents, projects)
                            except:
                                pass
                except:
                    print "   Error reading Stat"
                    traceback.print_exc()
            updatecount += 1
            if updatecount > 10 and len(insertstatement) > 0:
                self.backend.update_all_leaderstats(insertstatement)
                insertstatement = ""
                updatecount = 0
        if len(insertstatement) > 0:
            self.backend.update_all_leaderstats(insertstatement)
        self.backend.update_leaderupdate()
        print ""
        print("Update Stats Completed, Updating Names")
        for person in profiles:
            id = person["id"]
            try:
                profile = self.backend.get_profile(id, user)
                if "mugshot_urls" in profile:
                    if "thumb2" in profile["mugshot_urls"]:
                        mug = profile["mugshot_urls"]["thumb2"]
                    elif "small" in profile["mugshot_urls"]:
                        mug = profile["mugshot_urls"]["small"]
                    else:
                        mug = ""
                else:
                    mug = ""
                if "display_name" in profile:
                    name = profile["display_name"]
                else:
                    name = profile["name"]
                self.backend.update_leaderboard(id, name, mug)
            except:
                print("*** Error updating profile: " + id)
        print("Update Completed")


class ProjectUpdate(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        self.write("update initiated")
        self.finish()
        user = self.current_user
        if not user:
            user = {'id': self.settings.get("geni_app_id"), 'access_token': options.service_token, 'name': "HistoryLink App"}
        projects = self.backend.get_projectlist()
        for item in projects:
            try:
                print "Updating Project: " + item["name"]
            except:
                print "Updating Project: project-" + str(item["id"])
            self.backend.add_project(str(item["id"]), user)
        #Since there is a possible token refresh in the Geni Project API - check match
        if user and user["access_token"] != self.get_secure_cookie("access_token"):
            self.set_secure_cookie("access_token", user["access_token"])
            self.set_secure_cookie("refresh_token", user["refresh_token"])
        options.historyprofiles = set(self.backend.query_historyprofiles())


class ProjectSubmit(BaseHandler):
    @tornado.web.asynchronous
    @tornado.web.authenticated
    def post(self):
        project = self.get_argument("project", None)
        user = self.current_user
        try:
            logging.info(
                " *** " + str(user["name"]) + " (" + str(user["id"]) + ") submitted / updated project " + project)
        except:
            pass
        if not project:
            self.finish()
        args = {"user": user, "base": self, "project": project}
        ProjectWorker(self.worker_done, args).start()

    def worker_done(self, value):
        try:
            self.finish(value)
        except:
            return


class ProjectWorker(threading.Thread):
    user = None
    base = None
    project = None

    def __init__(self, callback=None, *args, **kwargs):
        self.user = args[0]["user"]
        self.base = args[0]["base"]
        self.project = args[0]["project"]
        args = {}
        super(ProjectWorker, self).__init__(*args, **kwargs)
        self.callback = callback

    def run(self):
        self.base.backend.add_project(self.project, self.user)
        options.historyprofiles = set(self.base.backend.query_historyprofiles())
        self.callback('DONE')


class ProjectHandler(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        try:
            validate = "https://www.geni.com/platform/oauth/validate_token?" + urllib.urlencode({
                "access_token": user["access_token"],
            })
            response = urllib.urlopen(validate)
            redata = response.read()
            if "error" in redata:
                self.redirect(self.get_refresh_token(self.request.uri))
                return
        except:
            self.redirect(self.get_login_url(self.request.uri))
            return

        delete = self.get_argument("delete", None)
        if delete:
            print "Deleting project-" + str(delete)
            self.backend.delete_project(delete)
            #self.backend.delete_links(delete)
        try:
            self.render("projects.html")
        except:
            return


class ProjectList(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        #projects = self.backend.query_projects()
        if not options.historyprofiles:
            options.historyprofiles = set(self.backend.query_historyprofiles())
        projects = []
        for item in sorted(options.historyprofiles):
            projects.append({"id": item, "name": options.historycache[item]})

        try:
            self.render("projectlist.html", projects=projects)
        except:
            return


class TreeComplete(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        cookie = self.application.linkHolder
        parentcount = cookie.getParentCount(user["id"])
        mpcount = cookie.get(user["id"], "mpcount")
        pending = cookie.get(user["id"], "pending")
        problems = cookie.get(user["id"], "problems")
        pconflict = cookie.get(user["id"], "pconflict")
        matchcount = cookie.get_matchcount(user["id"])
        count = cookie.get(user["id"], "count")

        gen = cookie.get(user["id"], "gen")
        self.render("treecomplete.html", parentcount=parentcount, gen=gen, mpcount=mpcount, pending=pending,
                    problems=problems, pconflict=pconflict, count=count, matchcount=matchcount)


class PrivacyHandler(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        self.render("privacypolicy.htm")


class BioHandler(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        self.render("biography.html")


class GraphHandler(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        try:
            validate = "https://www.geni.com/platform/oauth/validate_token?" + urllib.urlencode({
                "access_token": user["access_token"],
            })
            response = urllib.urlopen(validate)
            redata = response.read()
            if "error" in redata:
                self.redirect(self.get_refresh_token(self.request.uri))
                return
        except:
            self.redirect(self.get_login_url(self.request.uri))
            return

        profile_id = self.get_argument("profile", user["id"])
        if profile_id:
            info = self.backend.get_profile_info(profile_id, user)
            if info and "name" in info:
                username = info["name"]
            else:
                username = user["name"]
            if info and "id" in info:
                userid = info["id"]
            else:
                userid = user["id"]
            if info and "gender" in info:
                gender = info["gender"]
            else:
                gender = "unknown"
        else:
            username = user["name"]
            userid = user["id"]
            gender = "unknown"
        self.render("ancestorgraph.html", username=username, userid=userid, gender=gender)

    def worker_done(self, value):
        try:
            self.finish(value)
        except:
            return

    def post(self):
        import tornado_subprocess
        #import subprocess
        profile = self.get_argument("profile", None)
        type = self.get_argument("type", ".png")
        scale = self.get_argument("scale", "1")
        if not profile:
            user = self.current_user
            if not user:
                return
            profile = user["id"]
        cookie = self.application.linkHolder
        cookie.set(profile, "svg", self.request.body)
        filename = "AncestorGraph_" + profile + type
        hostpath = self.request.protocol + "://" + self.request.host + "/graphjs.svg?profile=" + profile
        args = ["phantomjs", "/static/js/graphrender.js", hostpath, filename, scale]
        #subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        t = tornado_subprocess.Subprocess(self.on_done(profile), timeout=5, args=args)
        t.start()
        return

    def on_done(self, profile, *args, **kwargs):
        print ("completed writing file")


class GraphJS(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        profile = self.get_argument("profile", None)
        if not profile:
            user = self.current_user
            if not user:
                return
            profile = user["id"]
        cookie = self.application.linkHolder
        data = cookie.get(profile, "svg")
        cookie.set(profile, "svg", None)
        self.set_header('Content-Type', 'image/svg+xml')
        self.write(data)
        self.finish()


class GraphRender(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        type = self.get_argument("type", ".png")
        profile = self.get_argument("profile", None)
        if not profile:
            user = self.current_user
            if not user:
                return
            profile = user["id"]
        filename = "AncestorGraph_" + profile + type
        logging.info("Graph Rendered for " + profile)
        i = 0
        while not os.path.isfile(filename):
            print ("Graph Render sleeping")
            time.sleep(0.3)
            i += 1
            if i > 15:
                print ("Faild to download file")
                self.write(
                    "<script>alert('There was a problem downloading file - timeout.  Please try again.');</script>")
                self.finish()
                return
        time.sleep(0.3)
        with open(filename, 'rb') as handle:
            data = handle.read()
        try:
            os.remove(filename)
        except OSError:
            pass
        if data:
            self.set_header('Pragma', 'public')
            self.set_header('Cache-Control', 'must-revalidate, post-check=0, pre-check=0')
            self.set_header('Expires', '-1')
            self.set_header('Content-Disposition', 'attachment; filename=AncestorGraph' + type)
            self.set_header('Content-Type', 'application/octet-stream')
            self.set_header('Content-Length', len(data))
            self.write(data)
            self.finish()
        return


class GraphProcess(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        profile = self.get_argument("profile", None)
        limit = int(self.get_argument("limit", 6))
        order = int(self.get_argument("order", 1))
        dna = self.get_argument("dna", None)
        adopt = self.get_argument("adopt", None)
        if adopt and adopt == "false":
            adopt = None
        elif adopt and adopt == "true":
            adopt = True
        if order == 1:
            dna = None
        if dna and dna == "all":
            dna = None
        user = self.current_user
        if not profile:
            profile = user["id"]
        if order == 1 and limit > 10:
            limit = 10
        elif limit > 15:
            limit = 15
        self.application.linkHolder.set(user["id"], "graphcount", 0)
        self.application.linkHolder.set(user["id"], "graphprofile", profile)
        self.application.linkHolder.set(user["id"], "graphlimit", limit - 1)
        self.application.linkHolder.set(user["id"], "graphorder", order)
        self.application.linkHolder.set(user["id"], "dna", dna)

        args = {"user": user, "base": self, "adopt": adopt}
        GraphWorker(self.worker_done, args).start()

    def worker_done(self, value):
        try:
            self.finish(value)
        except:
            return


class GraphCount(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        cookie = self.application.linkHolder
        result = self.get_argument("status", None)
        count = cookie.get(user["id"], "graphcount")
        pgcount = cookie.get(user["id"], "pgcount")
        status = cookie.get(user["id"], "graphrunning")
        error = cookie.get(user["id"], "accesserror")
        orderid = cookie.get(user["id"], "graphorder")
        cookie.set(user["id"], "accesserror", None)
        order = "Ancestors"
        if orderid:
            if orderid == 1:
                order = "Ancestors"
            else:
                order = "Descendants"
        if not count:
            count = 0
            pgcount = 0
        if result and result == "stop":
            status = 0
            cookie.set(user["id"], "graphrunning", 0)
        elif result and result == "start":
            status = 1
            cookie.set(user["id"], "json", 0)
            cookie.set(user["id"], "graphrunning", 1)
            cookie.set(user["id"], "graphcount", 0)
            cookie.set(user["id"], "pgcount", 0)
            count = 0
            pgcount = 0
        if not status:
            status = 0
        try:
            logging.info("  * " + str(user["name"]) + " (" + str(user["id"]) + "), " + order + ", Graph Gen: " + str(
                count) + ", " + str(pgcount) + " hits, Status: " + str(status))
        except:
            pass
        self.set_header("Cache-control", "no-cache")
        self.render("graphcount.html", count=count, status=status, error=error)

    @tornado.web.authenticated
    def post(self):
        user = self.current_user
        if user and "id" in user:
            self.application.linkHolder.set(user["id"], "graphrunning", 0)
        try:
            self.finish()
        except:
            return


class GraphList(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        cookie = self.application.linkHolder
        json = cookie.get(user["id"], "json")
        self.write(json)
        self.finish()


class HistoryHandler(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        try:
            validate = "https://www.geni.com/platform/oauth/validate_token?" + urllib.urlencode({
                "access_token": user["access_token"],
            })
            response = urllib.urlopen(validate)
            redata = response.read()
            if "error" in redata:
                self.redirect(self.get_refresh_token(self.request.uri))
                return
        except:
            self.redirect(self.get_login_url(self.request.uri))
            return

        profile_id = self.get_argument("profile", None)
        if profile_id:
            info = self.backend.get_profile_info(profile_id, user)
            if "name" in info:
                username = info["name"]
            else:
                username = user["name"]
            if "id" in info:
                userid = info["id"]
            else:
                userid = user["id"]
        else:
            username = user["name"]
            userid = user["id"]
        self.render("history.html", username=username, userid=userid)


class HistoryList(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        cookie = self.application.linkHolder
        matches = cookie.get_matches(user["id"])
        profile = self.get_argument("profile", None)
        hits = cookie.get(user["id"], "hits")
        showmatch = len(matches) - hits
        who = "is your"
        name = user["name"]
        if profile != user["id"]:
            who = None
            name = str(profile) + " (" + name + ")"
        i = 1
        projects = {}
        for item in matches:
            if item["message"]:
                if i > showmatch:
                    try:
                        logging.info(
                            " *** " + str(item["message"]) + " for " + name + " on " + str(item["id"]) + ": " + item[
                                "name"])
                    except:
                        pass
            else:
                if i > showmatch:
                    try:
                        pass
                        #logging.info(" *** Project Match for " +  name + " on " + str(item["id"]) + ": " + item["name"])
                    except:
                        pass
                for project in item["projects"]:
                    if project["id"] in projects:
                        projects[int(project["id"])]["count"] += 1
                    else:
                        projects[int(project["id"])] = {"count": 1, "name": project["name"]}
            i += 1
        cookie.reset_matchhit(user["id"])
        self.render("historylist.html", matches=matches, who=who, projects=projects)


class HistoryCount(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        user = self.current_user
        cookie = self.application.linkHolder
        result = self.get_argument("status", None)

        if result and result == "stop":
            #Note that fullStop() is called via Post, not Get (this might never run)
            status = 0
            cookie.stop(user["id"])
        elif result and result == "start":
            status = 1
            cookie.reset(user["id"])
            cookie.set(user["id"], "running", 1)
            stage = "parent's family"

        count = cookie.get(user["id"], "count")
        stage = cookie.get(user["id"], "stage")
        status = cookie.get(user["id"], "running")
        hits = cookie.get(user["id"], "hits")
        error = cookie.get(user["id"], "accesserror")
        cookie.set(user["id"], "accesserror", None)
        match = cookie.get_matchcount(user["id"])
        try:
            logging.info(
                "  * " + str(user["name"]) + " (" + str(user["id"]) + "), count: " + str(count) + " with " + str(
                    hits) + " hits, stage: " + str(stage))
        except:
            pass
        self.set_header("Cache-control", "no-cache")
        self.render("historycount.html", count=count, status=status, stage=stage, hits=hits, match=match, error=error)

    @tornado.web.authenticated
    def post(self):
        user = self.current_user
        if user and "id" in user:
            self.application.linkHolder.stop(user["id"])
        try:
            self.finish()
        except:
            return


class HistoryProcess(BaseHandler):
    @tornado.web.authenticated
    @tornado.web.asynchronous
    def get(self):
        profile = self.get_argument("profile", None)
        master = self.get_argument("master", None)
        project = self.get_argument("project", True)
        problem = self.get_argument("problem", None)
        complete = self.get_argument("complete", True)
        limit = self.get_argument("limit", None)
        siblings = self.get_argument("siblings", None)
        merges = self.get_argument("merges", None)
        follow = self.get_argument("follow", None)
        masterselect = self.get_argument("masterselect", True)
        followselect = self.get_argument("followselect", True)
        projectselect = self.get_argument("projectselect", "exlist")
        if master == "false":
            master = None
        if problem == "false":
            problem = None
        if project == "false":
            project = None
        if siblings == "false":
            siblings = None
        if masterselect == "false":
            masterselect = None
        if followselect == "false":
            followselect = None
        if complete == "false":
            complete = None
        if merges == "false":
            merges = None
        if follow == "false":
            follow = None
        user = self.current_user
        if not profile:
            profile = user["id"]
        if not options.historyprofiles:
            options.historyprofiles = set(self.backend.query_historyprofiles())

        cookie = self.application.linkHolder
        cookie.set(user["id"], "count", 0)
        cookie.set(user["id"], "running", 1)
        cookie.set(user["id"], "stage", "parent's family")
        cookie.set(user["id"], "master", master)
        cookie.set(user["id"], "project", project)
        cookie.set(user["id"], "problem", problem)
        cookie.set(user["id"], "complete", complete)
        cookie.set(user["id"], "follow", follow)
        cookie.set(user["id"], "limit", limit)
        cookie.set(user["id"], "siblings", siblings)
        cookie.set(user["id"], "merges", merges)
        cookie.set(user["id"], "masterselect", masterselect)
        cookie.set(user["id"], "projectselect", projectselect)
        cookie.set(user["id"], "followselect", followselect)
        cookie.set(user["id"], "rootprofile", profile)

        args = {"user": user, "base": self}
        HistoryWorker(self.worker_done, args).start()

    def worker_done(self, value):
        try:
            self.finish(value)
        except:
            return


class HistoryWorker(threading.Thread):
    def __init__(self, callback=None, *args, **kwargs):
        self.user = args[0]["user"]
        self.base = args[0]["base"]
        self.cookie = self.base.application.linkHolder
        args = {}
        super(HistoryWorker, self).__init__(*args, **kwargs)
        self.callback = callback

    def run(self):
        profile = self.user["id"]
        rootprofile = self.cookie.get(profile, "rootprofile")
        if not rootprofile:
            rootprofile = profile
        self.cookie.set_familyroot(profile, [rootprofile])
        limit = self.cookie.get(profile, "limit")
        #family_root.append(rootprofile)
        gen = 0
        self.setGeneration(gen)
        self.cookie.remove_parentmatch(profile, gen - 1)
        while len(self.cookie.get_familyroot(profile)) > 0:
            root = []
            root.extend(self.cookie.get_familyroot(profile))
            self.cookie.set_familyroot(profile, [])

            threads = 30
            profilesAtOnce = 6
            if not limit or int(limit) > gen:
                self.threadme(root, threads, profilesAtOnce)
                if len(self.cookie.get_familyroot(profile)) > 0:
                    gen += 1
                    self.setGeneration(gen)
            # Set the display for the completed Generation
        self.setGenerationLabel(gen - 1)
        self.cookie.set(profile, "running", 0)
        self.callback('DONE')

    def checkdone(self):
        if self.cookie.get(self.user["id"], "running") == 0:
            return True
        else:
            return False

    def setGeneration(self, gen):
        self.setGenerationLabel(gen)
        self.cookie.set(self.user["id"], "gen", gen)
        return

    def setGenerationLabel(self, gen):
        stage = str(self.cookie.getGeneration(gen)) + "'s family"
        self.cookie.set(self.user["id"], "stage", stage)
        return

    def checkmatch(self, family):
        match = []
        for item in family:
            if item in options.historyprofiles:
                match.append(item)
        return match

    def threadme(self, root, threadlimit=None, idlimit=10, timeout=0.05):
        assert threadlimit > 0, "need at least one thread";
        printlock = threading.Lock()
        threadpool = []

        # keep going while work to do or being done
        while root or threadpool:
            done = self.checkdone()
            if done:
                break
            parent_list = []
            # while there's room, remove source files
            # and add to the pool
            while root and (threadlimit is None or len(threadpool) < threadlimit):
                i = idlimit
                sub_root = []
                while i > 0:
                    sub_root.append(root.pop())
                    if len(root) > 0:
                        i -= 1
                    else:
                        i = 0
                wrkr = SubWorker(self, sub_root, printlock)
                wrkr.start()
                threadpool.append(wrkr)

            # remove completed threads from the pool
            for thr in threadpool:
                thr.join(timeout=timeout)
                if not thr.is_alive():
                    threadpool.remove(thr)
                    #print("all threads are done")


class SubWorker(threading.Thread):
    def __init__(self, root, family_list, printlock, **kwargs):
        super(SubWorker, self).__init__(**kwargs)
        self.root = root
        self.family_list = family_list
        self.lock = printlock # so threads don't step on each other's prints

    def run(self):
        #with self.lock:
        profile = self.root.user["id"]
        if not profile:
            return
        running = self.root.cookie.get(profile, "running")
        if running == 0:
            return
        the_group = self.root.base.backend.get_family_group(self.family_list, self.root.user)
        master = self.root.cookie.get(profile, "master")
        problem = self.root.cookie.get(profile, "problem")
        project = self.root.cookie.get(profile, "project")
        complete = self.root.cookie.get(profile, "complete")
        siblings = self.root.cookie.get(profile, "siblings")
        follow = self.root.cookie.get(profile, "follow")
        followselect = self.root.cookie.get(profile, "followselect")
        merges = self.root.cookie.get(profile, "merges")
        masterselect = self.root.cookie.get(profile, "masterselect")
        projectselect = self.root.cookie.get(profile, "projectselect")
        if the_group == "Invalid access token":
            self.root.cookie.stop(profile)
            self.root.base.set_secure_cookie("access_token", "")
            self.root.cookie.set(profile, "accesserror", True)
            the_group = None
        if the_group:
            for this_family in the_group:
                rematch = None
                rootprofile = None
                mastercount = 0
                mpcount = 0
                pendcount = 0
                pconflict = 0
                probcount = 0
                done = self.root.checkdone()
                if done:
                    break
                if isinstance(this_family, str):
                    logging.error("*** Family not Object: " + this_family)
                    if this_family == "Invalid access token":
                        self.root.cookie.stop(profile)
                        self.root.base.set_secure_cookie("access_token", "")
                        self.root.cookie.set(profile, "accesserror", True)
                    return
                parentscount = len(this_family.get_parents(2))
                adoptcount = len(this_family.get_parents(3))
                theparents = this_family.get_parents()

                if siblings:
                    #Exclude siblings
                    relatives = theparents
                else:
                    relatives = this_family.get_family_branch_group()
                gen = self.root.cookie.get(profile, "gen")

                if complete:
                    rootprofile = this_family.get_focus()
                    if not rootprofile:
                        continue
                    if parentscount > 2 or adoptcount > 2:
                        pconflict += 1
                        if problem:
                            projects = [None]
                            match = {"id": rootprofile, "relation": this_family.get_rel(gen - 1),
                                     "name": this_family.get_name(), "message": "Parent Conflict", "projects": projects}
                            self.root.cookie.add_matches(profile, match)
                        parentscount = 2

                for parent in theparents:
                    if parent.is_master():
                        mastercount += 1

                if rootprofile:
                    rootcount = self.root.cookie.get_parentmatch(profile, gen, rootprofile)
                    if rootcount == 0:
                        self.root.cookie.addParentCount(profile, gen, parentscount, mastercount)
                    else:
                        self.root.cookie.addParentCount(profile, gen, parentscount * rootcount, mastercount * rootcount)
                    for parent in theparents:
                        self.root.cookie.add_parentmatch(profile, gen + 1, parent.get_id())
                    while rootcount > 1:
                        rootcount -= 1
                        for parent in theparents:
                            self.root.cookie.add_parentmatch(profile, gen + 1, parent.get_id())
                for relative in relatives:
                    relativeprojects = relative.get_projects()
                    if (project or problem) and len(relativeprojects) > 0:
                        curatorexchange = 10985
                        projectlist = []
                        if projectselect == "exlist":
                            for id in relativeprojects:
                                #The goal here is to create an exclusion list to filter out unwanted projects
                                if problem and project:
                                    projectlist.append(id)
                                elif problem and id == curatorexchange:
                                    projectlist.append(id)
                                elif project and id != curatorexchange:
                                    projectlist.append(id)
                        elif projectselect == "inlist":
                            for id in relativeprojects:
                                if id in options.historyprofiles or id == curatorexchange:
                                    if problem and project:
                                        projectlist.append(id)
                                    elif problem and id == curatorexchange:
                                        projectlist.append(id)
                                    elif project and id != curatorexchange:
                                        projectlist.append(id)
                        else:
                            projectlist = relativeprojects

                        if len(projectlist) > 0:
                            projects = self.root.base.backend.get_projects(projectlist, self.root.user)
                            match = {"id": relative.get_id(), "relation": relative.get_rel(gen),
                                        "name": relative.get_name(), "message": False, "projects": projects}
                            rematch = self.root.cookie.add_matches(profile, match)

                    if master:
                        if masterselect and relative.is_master():
                            projects = [None]
                            match = {"id": relative.get_id(), "relation": relative.get_rel(gen),
                                     "name": relative.get_name(), "message": "Master Profile", "projects": projects}
                            rematch = self.root.cookie.add_matches(profile, match)
                        elif not masterselect and not relative.is_master() and relative.is_public():
                            projects = [None]
                            match = {"id": relative.get_id(), "relation": relative.get_rel(gen),
                                     "name": relative.get_name(), "message": "Non-Master Public", "projects": projects}
                            rematch = self.root.cookie.add_matches(profile, match)
                    if relative.merge_pending():
                        pendcount += 1
                        if merges:
                            projects = [None]
                            match = {"id": relative.get_id(), "relation": relative.get_rel(gen),
                                     "name": relative.get_name(), "message": "Merge Pending", "projects": projects}
                            rematch = self.root.cookie.add_matches(profile, match)
                    if problem and relative.get_message():
                        probcount += 1
                        projects = [None]
                        match = {"id": relative.get_id(), "relation": relative.get_rel(gen),
                                 "name": relative.get_name(), "message": relative.get_message(), "projects": projects}
                        self.root.cookie.add_matches(profile, match)
                        rematch = True
                    if relative.is_master():
                        mpcount += 1
                    if follow and followselect and relative.is_public():
                        self.root.base.backend.follow(relative.get_id(), self.root.user)
                    elif follow and relative.is_public():
                        self.root.base.backend.unfollow(relative.get_id(), self.root.user)

                count = int(self.root.cookie.get(profile, "count")) + len(relatives)
                probcount = self.root.cookie.get(profile, "problems") + probcount
                pendcount = self.root.cookie.get(profile, "pending") + pendcount
                mpcount = self.root.cookie.get(profile, "mpcount") + mpcount
                pconflict = self.root.cookie.get(profile, "pconflict") + pconflict
                self.root.cookie.set(profile, "problems", probcount)
                self.root.cookie.set(profile, "pconflict", pconflict)
                self.root.cookie.set(profile, "count", count)
                self.root.cookie.set(profile, "pending", pendcount)
                self.root.cookie.set(profile, "mpcount", mpcount)
                history = self.root.cookie.get_history(profile)
                for parent in theparents:
                    if not rematch and parent not in history:
                        self.root.cookie.append_familyroot(profile, parent.get_id())
                self.root.cookie.add_history(profile, self.root.cookie.get_familyroot(profile))

            if complete:
                for this_family in the_group:
                    rootprofile = this_family.get_focus()
                    if rootprofile:
                        theparents = this_family.get_parents()
                        parentscount = len(theparents)
                        gen = self.root.cookie.get(profile, "gen")
                        if not gen:
                            return
                        rootcount = self.root.cookie.get_parentmatch(profile, gen + 1, rootprofile)
                        if rootcount > 0:
                            self.root.cookie.addParentCount(profile, gen + 1, parentscount * rootcount,
                                                            mastercount * rootcount)
                            while rootcount > 0:
                                rootcount -= 1
                                for parent in theparents:
                                    self.root.cookie.add_parentmatch(profile, gen + 2, parent.get_id())


class GraphWorker(threading.Thread):
    def __init__(self, callback=None, *args, **kwargs):
        self.user = args[0]["user"]
        self.base = args[0]["base"]
        self.adopt = args[0]["adopt"]
        self.cookie = self.base.application.linkHolder
        self.geni = self.base.backend
        self.genstop = self.cookie.get(self.user["id"], "graphlimit")
        self.order = self.cookie.get(self.user["id"], "graphorder")
        self.dna = self.cookie.get(self.user["id"], "dna")
        self.genpos = 0
        self.json = ""
        self.countrylist = {}
        self.statelist = {}
        self.countryidx = 1
        self.stateidx = 1
        self.groupidx = 1
        self.uniqueid = random.random()
        self.cookie.set(self.user["id"], "uniqueid", self.uniqueid)
        args = {}
        super(GraphWorker, self).__init__(*args, **kwargs)
        self.callback = callback

    def run(self):
        profile = self.cookie.get(self.user["id"], "graphprofile") #"profile-34621975384"
        if not profile:
            profile = self.user["id"]
            #running = self.cookie.get(profile, "running")
            #if running == 0:
            #return

        if not options.countrycodes:
            import ast

            with open("countrycodes.txt", 'r') as handle:
                options.countrycodes = ast.literal_eval(handle.read().replace("\n", ""))
            with open("statecodes.txt", 'r') as handle:
                options.statecodes = ast.literal_eval(handle.read().replace("\n", ""))
        tree = Tree()
        person = None
        try:
            focusfamily = self.get_families(profile)
            if self.graphStopped() or self.deadProcess():
                return
            if isinstance(focusfamily, str):
                logging.error("*** Family not Object: " + focusfamily)
                if focusfamily == "Invalid access token":
                    self.base.set_secure_cookie("access_token", "")
                    self.cookie.set(self.user["id"], "accesserror", True)
                self.cookie.set(self.user["id"], "graphrunning", 0)
                return
            if len(focusfamily) < 1:
                logging.error("*** No Family in Array")
                self.cookie.set(self.user["id"], "graphrunning", 0)
                return
            family = focusfamily[0]
            if isinstance(family, str):
                logging.error("*** Family not Object: " + family)
                if family == "Invalid access token":
                    self.base.set_secure_cookie("access_token", "")
                    self.cookie.set(self.user["id"], "accesserror", True)
                self.cookie.set(self.user["id"], "graphrunning", 0)
                return
            person = family.get_person()
            person = self.geni.update_relative(person, self.user)
            if self.graphStopped():
                return
        except Exception as ex:
            try:
                #Give it a second try
                logging.info("Problem getting JSON from Geni - Trying Again")
                traceback.print_exc()
                focusfamily = self.geni.get_families(profile)
                if self.graphStopped() or self.deadProcess():
                    return
                if len(focusfamily) < 1:
                    logging.error("*** No Family in Array")
                    self.cookie.set(self.user["id"], "graphrunning", 0)
                    return
                family = focusfamily[0]
                if isinstance(family, str):
                    logging.error("*** Family not Object: " + family)
                    if family == "Invalid access token":
                        self.base.set_secure_cookie("access_token", "")
                        self.cookie.set(self.user["id"], "accesserror", True)
                    self.cookie.set(self.user["id"], "graphrunning", 0)
                    return
                person = family.get_person()
                person = self.geni.update_relative(person, self.user)
                if self.graphStopped() or self.deadProcess():
                    return
            except:
                logging.error("Problem getting JSON from Geni - Quiting")
                self.cookie.set(self.user["id"], "graphrunning", 2)
                return
        if not person:
            return

        gen = 0
        id = 0
        #tree = {}
        #parents = family.get_parents()
        #tree[str(gen)] = {str(id): family.get_person()}

        tree.create_node(person, person.get_id())  # root node
        rootparent = person

        tree_root = self.get_nextgen(family)
        if self.order == 1 and len(tree_root) == 1:
            tree.create_node("Blank", str(id), parent=person.get_id())
            tree_root.append(str(id))
            id += 1
        treecount = 0
        while len(tree_root) > 0:
            treecount += len(tree_root)
            if self.graphStopped() or self.deadProcess():
                return
                #print str(gen) + " : " + str(len(tree_root))
            sub_root = []
            sub_root.extend(tree_root)
            tree_root = []
            query_root = []
            family_root = []
            for idx, person in enumerate(sub_root):
                if self.graphStopped() or self.deadProcess():
                    return
                if not isinstance(person, str):
                    query_root.append(person.get_id())

            query_root = self.chunks(query_root, 50)
            for persons in query_root:
                #I think this is what takes a while - generate random number, save to cookie, check after to make sure it's the same.
                if self.graphStopped() or self.deadProcess():
                    #print ("*** quiting ****")
                    return
                try:
                    families = self.get_families(persons)
                except:
                    logging.info("Problem getting JSON from Geni - Trying Again 1")
                    traceback.print_exc()
                    try:
                        families = self.get_families(persons)
                    except:
                        logging.info("Problem getting JSON from Geni - Trying Again 2")
                        try:
                            families = self.get_families(persons)
                        except:
                            logging.info("Problem getting JSON from Geni - Quiting")
                            self.cookie.set(self.user["id"], "graphrunning", 2)
                            return
                family_root.extend(families)
            query_root = None
            sub_family = [None] * len(sub_root)

            for idx, person in enumerate(sub_root):
                if self.graphStopped() or self.deadProcess():
                    return
                if not isinstance(person, str):
                    if person.get_message() == "Access Denied":
                        sub_family[idx] = "Access Denied"
                    else:
                        for family in family_root:
                            if person.get_id() == family.get_focus():
                                sub_family[idx] = family
                                break
            family_root = None
            for idx, person in enumerate(sub_root):
                if self.graphStopped() or self.deadProcess():
                    return
                if isinstance(person, str):
                    cbase = tree.get_node(person)
                    if cbase.tag != "Denied":
                        tree.create_node("Blank", str(id), parent=person)
                        if gen < self.genstop:
                            tree_root.append(str(id))
                        id += 1
                        tree.create_node("Blank", str(id), parent=person)
                        if gen < self.genstop:
                            tree_root.append(str(id))
                        id += 1
                else:
                    cbase = tree.get_node(person.get_id())
                    if not cbase:
                        if self.order == 2:
                            if self.dna and self.dna != person.get_gender():
                                if person.is_living() and rootparent.get_gender() == "female":
                                    #mtDNA can be passed to males via the mother
                                    pass
                                else:
                                    continue
                        tree.create_node(person, person.get_id(), parent=rootparent.get_id())  # root node
                        cbase = tree.get_node(person.get_id())
                    child = cbase.tag

                    family = sub_family[idx]
                    if isinstance(family, str) and family == "Access Denied":
                        tree.create_node("Denied", str(id), parent=person.get_id())
                        if gen < self.genstop:
                            tree_root.append(str(id))
                        id += 1
                        continue
                    try:
                        #print family
                        parents = self.get_nextgen(family)
                        if self.graphStopped() or self.deadProcess():
                            return
                    except Exception, e:
                        logging.error("Problem getting JSON from Geni - Trying Again 1")
                        traceback.print_exc()
                        try:
                            parents = self.get_nextgen(family)
                        except:
                            logging.error("Problem getting JSON from Geni - Trying Again 2")
                            try:
                                parents = self.get_nextgen(family)
                            except:
                                logging.error("Problem getting JSON from Geni - Quiting")
                                self.cookie.set(self.user["id"], "graphrunning", 2)
                                return

                    if self.order == 1:
                        father = None
                        mother = None
                        if len(parents) > 2:
                            child.set_message(True) #parent conflict
                        for parent in parents:
                            rel = parent.get_gender()
                            if rel == "male":
                                father = parent
                            elif rel == "female":
                                mother = parent
                            else:
                                if not father:
                                    father = parent
                                elif not mother:
                                    mother = parent

                        if father:
                            if tree.get_node(father.get_id()):
                                pbase = tree.get_node(father.get_id())
                                parent = pbase.tag
                                if child.get_group() != "":
                                    parent.set_group(child.get_group())
                                else:
                                    parent.set_group(str(self.groupidx))
                                    self.groupidx += 1
                                    nextidx = parent.get_group()
                                    nextgen = pbase._bpointer
                                    for item in nextgen:
                                        edgecase = tree.get_node(item).tag
                                        if not isinstance(edgecase, str):
                                            edgecase.set_group(str(nextidx))
                            elif cbase and child.get_group() != "":
                                father.set_group(child.get_group())

                            if gen < self.genstop:
                                tree_root.append(father)
                            tree.create_node(father, father.get_id(), parent=person.get_id())
                            if father.get_message() == "Access Denied":
                                tree.create_node("Denied", str(id), parent=father.get_id())
                                if gen < self.genstop:
                                    tree_root.append(str(id))
                                id += 1
                        else:
                            if len(tree.get_node(person.get_id()).fpointer) < 2:
                                tree.create_node("Blank", str(id), parent=person.get_id())
                                if gen < self.genstop:
                                    tree_root.append(str(id))
                                id += 1

                        if mother:
                            if tree.get_node(mother.get_id()):
                                pbase = tree.get_node(mother.get_id())
                                parent = pbase.tag
                                if child.get_group() != "":
                                    parent.set_group(child.get_group())
                                else:
                                    parent.set_group(str(self.groupidx))
                                    self.groupidx += 1
                                    nextidx = parent.get_group()
                                    nextgen = pbase._bpointer
                                    for item in nextgen:
                                        edgecase = tree.get_node(item).tag
                                        if not isinstance(edgecase, str):
                                            edgecase.set_group(str(nextidx))
                            elif cbase and child.get_group() != "":
                                mother.set_group(child.get_group())

                            if gen < self.genstop:
                                tree_root.append(mother)
                            tree.create_node(mother, mother.get_id(), parent=person.get_id())
                            if mother.get_message() == "Access Denied":
                                tree.create_node("Denied", str(id), parent=mother.get_id())
                                if gen < self.genstop:
                                    tree_root.append(str(id))
                                id += 1
                        else:
                            if len(tree.get_node(person.get_id()).fpointer) < 2:
                                tree.create_node("Blank", str(id), parent=person.get_id())
                                if gen < self.genstop:
                                    tree_root.append(str(id))
                                id += 1
                    else:
                        for parent in parents:
                            if self.dna and self.dna != parent.get_gender():
                                if person.is_living() and child.get_gender() == "female":
                                    #mtDNA can be passed to males via the mother
                                    pass
                                else:
                                    continue
                            elif self.dna:
                                if child.get_gender() == self.dna:
                                    pass
                                else:
                                    continue
                            father = parent
                            if tree.get_node(father.get_id()):
                                pbase = tree.get_node(father.get_id())
                                parent = pbase.tag
                                if child.get_group() != "":
                                    parent.set_group(child.get_group())
                                else:
                                    parent.set_group(str(self.groupidx))
                                    self.groupidx += 1
                                    nextidx = parent.get_group()
                                    nextgen = pbase._bpointer
                                    for item in nextgen:
                                        edgecase = tree.get_node(item).tag
                                        if not isinstance(edgecase, str):
                                            edgecase.set_group(str(nextidx))
                            elif cbase and child.get_group() != "":
                                father.set_group(child.get_group())

                            if gen < self.genstop:
                                tree_root.append(father)
                            tree.create_node(father, father.get_id(), parent=person.get_id())
            self.genpos = gen
            gen += 1
            self.updateJSON(tree)
            if self.graphStopped() or self.deadProcess():
                return
            self.cookie.set(self.user["id"], "graphcount", gen)
            self.cookie.set(self.user["id"], "pgcount", treecount)
            #logging.info(self.cookie.get(self.user["id"], "json"))
        self.cookie.set(self.user["id"], "graphrunning", 0)

        self.callback('DONE')

    def get_families(self, persons):
        if self.order == 1:
            return self.geni.get_family_parents(persons, self.user)
        else:
            return self.geni.get_family_children(persons, self.user)

    def get_nextgen(self, family):
        if not family:
            return []
        if self.order == 1:
            if self.adopt:
                return family.get_parents(3)
            else:
                return family.get_parents(2)
        else:
            return family.get_children()

    def updateJSON(self, tree=None):
        self.json = ""
        self.processJSON(tree)
        if self.graphStopped() or self.deadProcess():
            return
        self.cookie.set(self.user["id"], "json", self.json)
        self.json = ""
        return

    def chunks(self, l, n):
        return [l[i:i + n] for i in range(0, len(l), n)]

    def deadProcess(self):
        return self.uniqueid != self.cookie.get(self.user["id"], "uniqueid")

    def graphStopped(self):
        return self.cookie.get(self.user["id"], "graphrunning") == 0

    def processJSON(self, tree=None, nid=None, level=None, idhidden=True, filter=None, cmp=None, key=None,
                    reverse=False):
        if self.graphStopped() or self.deadProcess():
            return
        if not tree:
            return
        if not level:
            level = tree.ROOT

        limit = self.genpos + 1
        if level > limit:
            return

        lasting = '{'

        nid = tree.root if (nid is None) else Node.sanitize_id(nid)
        person = tree[nid].tag
        parents = tree[nid].fpointer
        filter = tree._real_true if (filter is None) else filter

        bcountry = str(0)
        bstate = str(0)
        dcountry = str(0)
        dstate = str(0)
        denied = str(0)
        deathlocation = ""
        deathdate = ""
        deathcirca = ""
        living = str(0)
        if person == "Blank":
            name = ""
            gender = str(0)
            master = str(0)
            public = str(0)
            claimed = str(0)
            conflict = str(0)
            birthdate = ""
            birthcirca = ""
            birthlocation = ""
            id = ""
            group = ""
        elif person == "Denied":
            name = ""
            gender = str(3)
            master = str(0)
            public = str(0)
            claimed = str(0)
            conflict = str(1)
            denied = str(1)
            birthdate = ""
            birthcirca = ""
            birthlocation = ""
            id = ""
            group = ""
        else:
            if person.is_living():
                living = str(1)
            rel = person.get_gender()
            if rel == "female":
                gender = str(1)
            elif rel == "male":
                gender = str(2)
            else:
                gender = str(3)
            name = person.get_name()
            if name:
                name = name.replace('"', "'")
            else:
                name = ""
            master = str(1) if person.is_master() else str(0)
            public = str(1) if person.is_public() else str(0)
            claimed = str(1) if person.is_claimed() else str(0)
            conflict = str(0)
            if person.get_message() and person.get_message() != "Access Denied":
                conflict = str(1)

            birthdate = person.get_birth_date()
            birthcirca = person.get_birth_circa()
            birthlocation = person.get_birth_location()
            id = person.get_id()
            group = person.get_group()
            countryvar = person.get_birth_country()
            statevar = person.get_birth_state()
            if countryvar:
                if len(countryvar) > 2:
                    countryvar = countryvar.replace("(", "").strip()
                    countryvar = countryvar.replace(")", "").strip()
                    countryvar = countryvar.replace("Present", "").strip()
                    if countryvar in options.countrycodes:
                        countryvar = options.countrycodes[countryvar]
                elif countryvar == "UK":
                    countryvar = "GB"
                if not countryvar in self.countrylist:
                    self.countrylist[countryvar] = str(self.countryidx)
                    self.countryidx += 1
                bcountry = self.countrylist[countryvar]
            if statevar:
                if len(statevar) == 2:
                    if statevar in options.statecodes:
                        statevar = options.statecodes[statevar]
                if not statevar in self.statelist:
                    self.statelist[statevar] = str(self.stateidx)
                    self.stateidx += 1
                bstate = self.statelist[statevar]
            if not person.is_living():
                deathdate = person.get_death_date()
                deathcirca = person.get_death_circa()
                deathlocation = person.get_death_location()
                countryvar = person.get_death_country()
                statevar = person.get_death_state()
                if countryvar:
                    if len(countryvar) > 2:
                        countryvar = countryvar.replace("(", "").strip()
                        countryvar = countryvar.replace(")", "").strip()
                        countryvar = countryvar.replace("Present", "").strip()
                        if countryvar in options.countrycodes:
                            countryvar = options.countrycodes[countryvar]
                    elif countryvar == "UK":
                        countryvar = "GB"
                    if not countryvar in self.countrylist:
                        self.countrylist[countryvar] = str(self.countryidx)
                        self.countryidx += 1
                    dcountry = self.countrylist[countryvar]
                if statevar:
                    if len(statevar) == 2:
                        if statevar in options.statecodes:
                            statevar = options.statecodes[statevar]
                    if not statevar in self.statelist:
                        self.statelist[statevar] = str(self.stateidx)
                        self.stateidx += 1
                    dstate = self.statelist[statevar]

        if level == tree.ROOT:
            self.json += lasting + '"name": "' + name + \
                         '", ' + '"mp": ' + master + \
                         ', ' + '"pb": ' + public + \
                         ', ' + '"cl": ' + claimed + \
                         ', ' + '"pc": ' + conflict + \
                         ', ' + '"ad": ' + denied + \
                         ', ' + '"id": "' + id + \
                         '", ' + '"bd": "' + birthdate + \
                         '", ' + '"bc": "' + birthcirca + \
                         '", ' + '"dd": "' + deathdate + \
                         '", ' + '"dc": "' + deathcirca + \
                         '", ' + '"bl": "' + birthlocation + \
                         '", ' + '"dl": "' + deathlocation + \
                         '", ' + '"gp": "' + group + \
                         '", ' + '"ct": "' + bcountry + \
                         '", ' + '"st": "' + bstate + \
                         '", ' + '"cd": "' + dcountry + \
                         '", ' + '"sd": "' + dstate + \
                         '", ' + '"gd": "' + gender + \
                         '", ' + '"lv": "' + living + \
                         '", "children": [' #\n'

        else:
            if len(parents) > 0 and level < limit:
                #str((level) * "\t") + " " +
                self.json += lasting + '"name": "' + name + \
                             '", ' + '"mp": ' + master + \
                             ', ' + '"pb": ' + public + \
                             ', ' + '"cl": ' + claimed + \
                             ', ' + '"pc": ' + conflict + \
                             ', ' + '"ad": ' + denied + \
                             ', ' + '"id": "' + id + \
                             '", ' + '"bd": "' + birthdate + \
                             '", ' + '"bc": "' + birthcirca + \
                             '", ' + '"dd": "' + deathdate + \
                             '", ' + '"dc": "' + deathcirca + \
                             '", ' + '"bl": "' + birthlocation + \
                             '", ' + '"dl": "' + deathlocation + \
                             '", ' + '"gp": "' + group + \
                             '", ' + '"ct": "' + bcountry + \
                             '", ' + '"st": "' + bstate + \
                             '", ' + '"cd": "' + dcountry + \
                             '", ' + '"sd": "' + dstate + \
                             '", ' + '"gd": "' + gender + \
                             '", ' + '"lv": "' + living + \
                             '", "children": [' #\n'
            else:
                #str((level) * "\t") + " " +
                self.json += lasting + '"name": "' + name + \
                             '", ' + '"mp": ' + master + \
                             ', ' + '"pb": ' + public + \
                             ', ' + '"cl": ' + claimed + \
                             ', ' + '"pc": ' + conflict + \
                             ', ' + '"ad": ' + denied + \
                             ', ' + '"id": "' + id + \
                             '", ' + '"bd": "' + birthdate + \
                             '", ' + '"bc": "' + birthcirca + \
                             '", ' + '"bl": "' + birthlocation + \
                             '", ' + '"dd": "' + deathdate + \
                             '", ' + '"dc": "' + deathcirca + \
                             '", ' + '"dl": "' + deathlocation + \
                             '", ' + '"gp": "' + group + \
                             '", ' + '"ct": "' + bcountry + \
                             '", ' + '"st": "' + bstate + \
                             '", ' + '"cd": "' + dcountry + \
                             '", ' + '"sd": "' + dstate + \
                             '", ' + '"gd": "' + gender + \
                             '", ' + '"lv": "' + living + '"}'
        self.json = self.json.replace("[,{", "[{")
        if filter(tree[nid]) and tree[nid].expanded:
            queue = [tree[i] for i in tree[nid].fpointer if filter(tree[i])]
            #key = (lambda x: x) if (key is None) else key
            #queue.sort(cmp=cmp, key=key, reverse=reverse)
            level += 1
            if level <= limit:
                for idx, element in enumerate(queue):
                    if self.graphStopped() or self.deadProcess():
                        return

                    if self.order == 1 and idx == len(queue) - 1:
                        #self.json += ",\n"
                        self.json += ","
                    elif self.order == 2 and idx > 0:
                        self.json += ","

                    self.processJSON(tree, element.identifier, level, idhidden, filter, cmp, key, reverse)
                    if idx == len(queue) - 1:
                        pass
                        #self.json += "\n"
        if len(parents) > 0 and level <= limit:
            self.json += ']}'
            #self.json += str((level-1) * "\t") + ']}'

    def checkdone(self):
        if self.cookie.get(self.user["id"], "running") == 0:
            return True
        else:
            return False

    def setGeneration(self, gen):
        self.setGenerationLabel(gen)
        self.cookie.set(self.user["id"], "gen", gen)
        return


class LoginHandler(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        next = self.get_argument("next", None)
        code = self.get_argument("code", None)
        if not next:
            self.redirect(self.get_login_url(self.reverse_url("home")))
            return
        if not next.startswith("https://" + self.request.host + "/") and \
                not next.startswith("http://" + self.request.host + "/") and \
                not next.startswith("http%3A%2F%2F" + self.request.host + "/") and \
                not next.startswith("https%3A%2F%2F" + self.request.host + "/") and \
                not next.startswith(self.settings.get("geni_canvas_id")) and \
                not next.endswith(self.settings.get("geni_app_id")):
            raise tornado.web.HTTPError(
                404, "Login redirect (%s) spans hosts", next)
        if self.get_argument("error", None):
            logging.warning("Geni login error: %r", self.request.arguments)
            self.set_error_message(
                "An Login error occured with Geni. Please try again later.")
            self.redirect(self.reverse_url("home"))
            return
        if not code:
            self.redirect(self.get_login_url(next))
            return
        next = next.replace("http:", self.request.protocol + ":")
        redirect_uri = self.request.protocol + "://" + self.request.host + \
                       self.request.path + "?" + urllib.urlencode({"next": next})
        url = "https://www.geni.com/platform/oauth/request_token?" + \
              urllib.urlencode({
                  "client_id": self.settings.get("geni_app_id"),
                  "client_secret":self.settings.get("geni_secret"),
                  "redirect_uri": redirect_uri,
                  "code": code,
              })
        client = tornado.httpclient.AsyncHTTPClient()
        client.fetch(url, self.on_access_token)

    def on_access_token(self, response):
        if response.error:
            print response
            self.set_error_message(
                "An error occured with Geni. Error: " + response.error + " Please try again later.")
            self.redirect(self.reverse_url("home"))
            return
        mytoken = json.loads(response.body)
        access_token = mytoken["access_token"]
        refresh_token = mytoken["refresh_token"]
        url = "https://www.geni.com/api/profile?" + urllib.urlencode({
            "access_token": access_token,
        })
        client = tornado.httpclient.AsyncHTTPClient()
        client.fetch(url, functools.partial(self.on_profile, access_token, refresh_token))

    def on_profile(self, access_token, refresh_token, response):
        if response.error:
            self.set_error_message(
                "A profile response error occured with Geni.  Error: " + response.error + " Please try again later.")
            self.redirect(self.reverse_url("home"))
            return
        profile = json.loads(response.body)
        if not profile:
            self.redirect(self.reverse_url("home"))
            return
        self.set_secure_cookie("uid", profile["id"])
        self.set_secure_cookie("name", profile["name"])
        self.set_secure_cookie("access_token", access_token)
        self.set_secure_cookie("refresh_token", refresh_token)
        if "account_type" in profile:
            self.set_secure_cookie("account_type", profile["account_type"])
        else:
            self.set_secure_cookie("account_type", "basic")
        if "big_tree" in profile:
            self.set_secure_cookie("big_tree", str(profile["big_tree"]))
        else:
            self.set_secure_cookie("big_tree", "False")
        self.redirect(self.get_argument("next", self.reverse_url("home")))
        return


class LogoutHandler(BaseHandler):
    @tornado.web.asynchronous
    def get(self):
        redirect_uri = self.request.protocol + "://" + self.request.host
        user = self.current_user
        access_token = user["access_token"]
        cookie = self.application.linkHolder
        cookie.stop(user["id"])
        self.set_secure_cookie("access_token", "")
        self.set_secure_cookie("uid", "")
        urllib.urlopen("https://www.geni.com/platform/oauth/invalidate_token?" + urllib.urlencode({
            "access_token": access_token
        }))
        self.redirect(redirect_uri)


class GeniCanvasHandler(HomeHandler):
    @tornado.web.asynchronous
    def get(self, *args, **kwds):
        logging.info("Geni Canvas called.")
        if not self.current_user:
            self.login(self.settings.get("geni_canvas_id"))
        else:
            super(GeniCanvasHandler, self).get(*args, **kwds)


class Backend(object):
    def __init__(self):
        self.db = torndb.Connection(
            host=options.mysql_host, database=options.mysql_database,
            user=options.mysql_user, password=options.mysql_password)

    @classmethod
    def instance(cls):
        if not hasattr(cls, "_instance"):
            cls._instance = cls()
        return cls._instance

    def get_family(self, profile, user):
        geni = self.get_API(user)
        return geni.get_family(profile, True, True, True, True)

    def get_family_detailed(self, profile, user):
        geni = self.get_API(user)
        return geni.get_family_detailed(profile, True, True, True, True)

    def get_profile_detailed(self, profile, user):
        geni = self.get_API(user)
        return geni.get_profile_detailed(profile)

    def get_profile(self, profile, user):
        geni = self.get_API(user)
        return geni.get_profile(profile)

    def get_family_group(self, family_root, user):
        geni = self.get_API(user)
        return geni.get_family_group(family_root)

    def follow(self, profile, user):
        geni = self.get_API(user)
        return geni.follow_profile(profile)

    def unfollow(self, profile, user):
        geni = self.get_API(user)
        return geni.unfollow_profile(profile)

    def get_family_parents(self, family_root, user):
        geni = self.get_API(user)
        return geni.get_family_parents(family_root)

    def update_relative(self, relative, user):
        geni = self.get_API(user)
        return geni.update_relative(relative)

    def get_family_children(self, family_root, user):
        geni = self.get_API(user)
        return geni.get_family_children(family_root)

    def get_master(self, profiles, user):
        geni = self.get_API(user)
        return geni.get_master(profiles)

    def update_leaderboard(self, id, name, mug):
        self.db.reconnect()
        try:
            if mug.startswith("http://photo.geni.com") or mug.startswith("https://photo.geni.com") or mug.startswith("https://s3.amazonaws.com"):
                self.db.execute(
                    "INSERT INTO curators (id, name, mug) VALUES (%s,%s,%s) "
                    "ON DUPLICATE KEY UPDATE name=%s,mug=%s", id, name, mug)
            else:
                mug = "https://geni1-mhcache-com-myheritage.netdna-ssl.com/images/no_photo_u.gif"
                self.db.execute(
                    "INSERT INTO curators (id, name, mug) VALUES (%s,%s,%s) "
                    "ON DUPLICATE KEY UPDATE name=%s,mug=%s", id, name, mug)
        except:
            if mug.startswith("http://photo.geni.com") or mug.startswith("https://photo.geni.com") or mug.startswith("https://s3.amazonaws.com"):
                self.db.execute(
                    "INSERT INTO curators (id, name, mug) VALUES (%s,%s,%s) "
                    "ON DUPLICATE KEY UPDATE name=%s,mug=%s", id, name, mug)
            else:
                mug = "https://geni1-mhcache-com-myheritage.netdna-ssl.com/images/no_photo_u.gif"
                self.db.execute(
                    "INSERT INTO curators (id, name, mug) VALUES (%s,%s,%s) "
                    "ON DUPLICATE KEY UPDATE name=%s,mug=%s", id, name, mug)
        return

    def update_all_leaderstats(self, query):
        try:
            self.db.execute(query)
        except:
            self.db.execute(query)
        return

    def update_leaderupdate(self):
        self.db.reconnect()
        now = datetime.now()
        tzlong = time.strftime("%Z")
        tz = " EST"
        if tzlong == "Eastern Daylight Time":
            tz = " EDT"
        timestamp = now.strftime("%Y-%m-%d %H:%M") + tz
        try:
            self.db.execute("UPDATE leaderupdate SET updatetime=%s WHERE id=1", timestamp)
        except:
            self.db.execute("UPDATE leaderupdate SET updatetime=%s WHERE id=1", timestamp)
        return

    def get_leaderupdate(self):
        self.db.reconnect()
        try:
            return self.db.query("SELECT updatetime FROM leaderupdate WHERE id=1")
        except:
            return self.db.query("SELECT updatetime FROM leaderupdate WHERE id=1")

    def get_curators(self, curator=None):
        if curator:
            self.db.reconnect()
            try:
                return self.db.query("SELECT id,userid,name,exclude FROM curators WHERE id=%s AND disable=0", curator)
            except:
                return self.db.query("SELECT id,userid,name,exclude FROM curators WHERE id=%s AND disable=0", curator)
        else:
            try:
                return self.db.query("SELECT id,userid,name FROM curators WHERE disable=0 ORDER BY name")
            except:
                return self.db.query("SELECT id,userid,name FROM curators WHERE disable=0 ORDER BY name")

    def get_merge_leaders(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.merges FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY merges DESC LIMIT 100',
                timeframe)
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.merges FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY merges DESC LIMIT 100',
                timeframe)

    def get_add_leaders(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.additions FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY additions DESC LIMIT 100',
                timeframe)
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.additions FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY additions DESC LIMIT 100',
                timeframe)

    def get_doc_leaders(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.document FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY document DESC LIMIT 100',
                timeframe)
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.document FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY document DESC LIMIT 100',
                timeframe)

    def get_project_leaders(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.projects FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY projects DESC LIMIT 100',
                timeframe)
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.projects FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY projects DESC LIMIT 100',
                timeframe)

    def get_merge_total(self):
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.merges) AS merges FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY merges DESC LIMIT 100')
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.merges) AS merges FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY merges DESC LIMIT 100')

    def get_add_total(self):
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.additions) AS additions FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY additions DESC LIMIT 100')
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.additions) AS additions FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY additions DESC LIMIT 100')

    def get_doc_total(self):
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.document) AS document FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY document DESC LIMIT 100')
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.document) AS document FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY document DESC LIMIT 100')

    def get_project_total(self):
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.projects) AS projects FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY projects DESC LIMIT 100')
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, sum(leaderstats.projects) AS projects FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY projects DESC LIMIT 100')

    def get_curator_stats(self):
        try:
            return self.db.query(
                'SELECT timeframe, SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats GROUP BY timeframe')
        except:
            return self.db.query(
                'SELECT timeframe, SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats GROUP BY timeframe')

    def get_curator_total(self):
        try:
            return self.db.query(
                'SELECT SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats')
        except:
            return self.db.query(
                'SELECT SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats')

    def get_update_leaders(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.updates FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY updates DESC LIMIT 100',
                timeframe)
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, leaderstats.updates FROM curators, leaderstats WHERE curators.id=leaderstats.id AND leaderstats.timeframe=%s AND curators.exclude=0 ORDER BY updates DESC LIMIT 100',
                timeframe)

    def get_update_total(self):
        try:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, SUM(leaderstats.updates) AS updates FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY updates DESC LIMIT 100')
        except:
            return self.db.query(
                'SELECT curators.id, curators.name, curators.mug, SUM(leaderstats.updates) AS updates FROM curators, leaderstats WHERE curators.id=leaderstats.id AND curators.exclude=0 GROUP BY curators.id ORDER BY updates DESC LIMIT 100')


    def get_curator_counts(self, timeframe=None):
        if not timeframe:
            d = datetime.now()
            timeframe = str(d.year) + "-" + str('%02d' % d.month)
        try:
            return self.db.query(
                "SELECT SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats WHERE timeframe=%s",
                timeframe)
        except:
            return self.db.query(
                "SELECT SUM(merges) AS merges, SUM(updates) AS updates, SUM(additions) AS additions, SUM(document) AS documentation, SUM(projects) AS projects FROM leaderstats WHERE timeframe=%s",
                timeframe)

    def add_project(self, project_id, user):
        if not user:
            return
        if not project_id:
            return
        if not project_id.isdigit():
            return

        projectname = self.get_project_name(project_id, user)

        #geni = self.get_API(user)
        # projectprofiles = None
        # try:
        #     projectprofiles = geni.get_project_profiles(project_id)
        # except:
        #     traceback.print_exc()
        # if geni.access_token:
        #     user["access_token"] = geni.access_token
        #     user["refresh_token"] = geni.refresh_token
        # if projectprofiles and len(projectprofiles) > 0:
        #     pass
        # else:
        #     return
        #self.delete_project(project_id)
        try:
            self.db.execute(
                "INSERT INTO projects (id, name) VALUES (%s,%s) "
                "ON DUPLICATE KEY UPDATE name=%s", project_id, projectname, projectname)
        except:
            self.db.execute(
                "INSERT INTO projects (id, name) VALUES (%s,%s) "
                "ON DUPLICATE KEY UPDATE name=%s", project_id, projectname, projectname)

        # chunks = self.chunks(projectprofiles, 1000) #Only send 1000 to the DB at one time
        # projectprofiles = None
        # if chunks and len(chunks) > 0:
        #     self.delete_links(project_id)
        # else:
        #     return
        # for projectprofiles in chunks:
        #     query = ""
        #     for item in projectprofiles:
        #         query += '(' + project_id + ',"' + str(item["id"]) + '"),'
        #     query = "INSERT IGNORE INTO links (project_id,profile_id) VALUES " + query[:-1]
        #     try:
        #         self.db.execute(query)
        #     except:
        #         self.db.execute(query)
        # try:
        #     profilecount = self.db.query("SELECT COUNT(profile_id) FROM links WHERE project_id = %s", project_id)
        # except:
        #     profilecount = self.db.query("SELECT COUNT(profile_id) FROM links WHERE project_id = %s", project_id)
        # if not profilecount:
        #     return
        # if "COUNT(profile_id)" in profilecount[0]:
        #     self.db.execute("UPDATE projects SET count=%s WHERE id=%s", int(profilecount[0]["COUNT(profile_id)"]),
        #                     project_id)
        return

    def chunks(self, l, n):
        return [l[i:i + n] for i in range(0, len(l), n)]

    def get_project_profiles(self, project, user):
        geni = self.get_API(user)
        project = geni.get_project_profiles(project)
        return project

    def get_profile_name(self, profile, user):
        geni = self.get_API(user)
        return geni.get_profile_name(profile)

    def get_profile_info(self, profile, user):
        geni = self.get_API(user)
        return geni.get_profile_info(profile)

    def get_project_name(self, project, user):
        geni = self.get_API(user)
        return geni.get_project_name(project)

    def get_projects(self, projects, user):
        geni = self.get_API(user)
        result = geni.get_projects(projects)
        return result

    def get_geni_request(self, path, user, args=None, post_args=None, post_data=None):
        geni = self.get_API(user)
        return geni.request(str(path), args, post_args, post_data)

    def get_API(self, user):
        if user:
            access_token = user['access_token']
            refresh_token = user['refresh_token']
        else:
            app_id = options.historylink_id
            geni_secret = options.historylink_secret
            access_token = app_id + "|" + geni_secret
            refresh_token = None
        giniapi = geni.GeniAPI(access_token, refresh_token, options)
        return giniapi

    def query_historyprofiles(self):
        result = None
        self.db.reconnect()
        try:
            result = self.db.query("SELECT id,name FROM projects ORDER BY id")
        except:
            result = self.db.query("SELECT id,name FROM projects ORDER BY id")
        if not result:
            return result
        projectlist = []
        if not options.historycache:
            options.historycache = {}
        for item in result:
            projectlist.append(item["id"])
            if not item["id"] in options.historycache:
                options.historycache[item["id"]] = item["name"]
        return projectlist


    def get_projectlist(self):
        self.db.reconnect()
        try:
            projects = self.db.query("SELECT id,name FROM projects")
        except:
            projects = self.db.query("SELECT id,name FROM projects")
        return projects

    def delete_project(self, id):
        if id:
            id = id.replace("project-", "")
            self.db.reconnect()
            try:
                self.db.execute("DELETE FROM projects WHERE id=%s", id)
            except:
                self.db.execute("DELETE FROM projects WHERE id=%s", id)
        return

    #
    # def query_projects(self):
    #     result = None
    #     self.db.reconnect()
    #     try:
    #         result = self.db.query("SELECT * FROM projects ORDER BY id")
    #     except:
    #         result = self.db.query("SELECT * FROM projects ORDER BY id")
    #     return result
    # def delete_links(self, id):
    #     self.db.reconnect()
    #     if id:
    #         try:
    #             self.db.execute("DELETE FROM links WHERE project_id=%s", id)
    #         except:
    #             self.db.execute("DELETE FROM links WHERE project_id=%s", id)
    #     return

    # def get_history_profiles(self):
    #     self.db.reconnect()
    #     try:
    #         profiles = self.db.query("SELECT DISTINCT profile_id FROM links")
    #     except:
    #         profiles = self.db.query("SELECT DISTINCT profile_id FROM links")
    #     logging.info("Building history profile list.")
    #     profilelist = []
    #     for item in profiles:
    #         profilelist.append(item["profile_id"])
    #     return profilelist

    # def get_db_projects(self, id, project=None, problem=None):
    #     self.db.reconnect()
    #     try:
    #         projects = self.db.query(
    #             "SELECT links.project_id, projects.name FROM links, projects WHERE links.project_id=projects.id AND links.profile_id = %s",
    #             id)
    #     except:
    #         projects = self.db.query(
    #             "SELECT links.project_id, projects.name FROM links, projects WHERE links.project_id=projects.id AND links.profile_id = %s",
    #             id)
    #     projectlist = []
    #     for item in projects:
    #         if problem and project:
    #             projectlist.append({"id": item["project_id"], "name": item["name"]})
    #         elif problem and item["project_id"] == 10985:
    #             projectlist.append({"id": item["project_id"], "name": item["name"]})
    #         elif project and item["project_id"] != 10985:
    #             projectlist.append({"id": item["project_id"], "name": item["name"]})
    #     return projectlist
    #
    # def get_profile_count(self):
    #     self.db.reconnect()
    #     profilecount = None
    #     count = 0
    #     try:
    #         profilecount = self.db.query("SELECT DISTINCT COUNT(profile_id) FROM links")
    #     except:
    #         profilecount = self.db.query("SELECT DISTINCT COUNT(profile_id) FROM links")
    #     if profilecount and "COUNT(profile_id)" in profilecount[0]:
    #         count = "{:,.0f}".format(int(profilecount[0]["COUNT(profile_id)"]))
    #     return count


class TimeConvert(tornado.web.UIModule):
    def render(self, dt):
        return str(time.mktime(dt.timetuple()))


class SHAHash(tornado.web.UIModule):
    def render(self, shared_private_key, data):
        return hashlib.sha1(repr(data) + "," + shared_private_key).hexdigest()


class ResponseItem(tornado.web.UIModule):
    def render(self, response):
        return response


def load_signed_request(signed_request, app_secret):
    try:
        sig, payload = signed_request.split(u'.', 1)
        sig = base64_url_decode(sig)
        data = json.loads(base64_url_decode(payload))

        expected_sig = hmac.new(app_secret, msg=payload, digestmod=hashlib.sha256).digest()

        if sig == expected_sig and data[u'issued_at'] > (time.time() - 86400):
            return data
        else:
            return None
    except ValueError, ex:
        return None


def base64_url_decode(data):
    data = data.encode(u'ascii')
    data += '=' * (4 - (len(data) % 4))
    return base64.urlsafe_b64decode(data)


def self(args):
    pass


def main():
    tornado.options.parse_command_line()
    options.historyprofiles = None
    if options.config:
        tornado.options.parse_config_file(options.config)
    else:
        path = os.path.join(os.path.dirname(__file__), "settings.py")
        tornado.options.parse_config_file(path)
    from tornado.httpserver import HTTPServer
    from tornado.ioloop import IOLoop
    #from tornado.wsgi import WSGIContainer
    #http_server = HTTPServer(WSGIContainer(GeniApplication()))
    http_server = HTTPServer(GeniApplication(), xheaders=True)
    #http_server.listen(8080)
    http_server.listen(int(os.environ.get("PORT", 80)))
    IOLoop.instance().start()


if __name__ == "__main__":
    main()
